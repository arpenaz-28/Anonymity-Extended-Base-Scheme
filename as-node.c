/* ==========================================================================
 * as-node.c  —  Authentication Server
 *
 * Implements the EXACT protocol specified:
 *
 * PHASE 1 — ENROLLMENT
 *   Reg-0: Device sends AES_enc(K_AS_D, [id_d | pad]) = 16 B
 *           AS replies  AES_enc(K_AS_D, [c_d | m_d(32) | pad]) = 48 B
 *           AS stores: fresh random c_d AND fresh random m_d per device.
 *
 *   Reg-1: Device sends AES_enc(K_AS_D, [id_d | y_dH(32) | R_d | c_as_d | pad]) = 48 B
 *           AS:  T_acc = T_acc & y_dH
 *                R_as = PUF(c_as_d)
 *                phi_as_d = R_as XOR R_d
 *                PID_curr = H(ID||m_curr);  PID_old = none;
 *                m_curr = m_d (received m_d stored, this is m_curr);
 *                m_old  = none (pid_old_valid = 0)
 *
 * PHASE 2 — AUTHENTICATION
 *   Device sends: PID(32) | y_asd(32) | ts_1(1) = 65 B (plain – PID gives anon)
 *   AS:
 *     a. Search PID_curr / PID_old across all clients.
 *     b. Freshness check: ts_1 strictly ahead of last seen ts_1.
 *     c. R_as = PUF(c_as_d);  R_d = phi_as_d XOR R_as
 *     d. mask = H(R_d || m_active || PID || ts_1)
 *        y_dH = y_asd XOR mask
 *     e. Membership: T_new = T_acc & y_dH;  accept iff T_new == T_acc
 *
 * PHASE 3 — KEY EXCHANGE (immediately after Phase 2, same handler)
 *   a. Generate random n1(32 B);  ts_2 = clock();  m_new = H(n1)
 *   b. mH_mask = H(y_dH || m_active || R_d || ID_AS || PID || ts_2)
 *      m_H = m_new XOR mH_mask          ← sent to device to recover m_new
 *   c. K_GW_D = H(R_d || m_new)
 *   d. ts_auth = clock()
 *      token = AES_enc(K_GW_AS, [ID_d | ID_AS | ts_auth | pad(13)]) ||
 *              AES_enc(K_GW_AS, K_GW_D[0..15])                       ||
 *              AES_enc(K_GW_AS, K_GW_D[16..31])   (= 48 B)
 *   e. Pseudonym rotation:
 *        PID_old  = PID_curr;  PID_curr  = H(ID || m_new)
 *        m_old    = m_curr;    m_curr    = m_new
 *   f. Reply to device: ACK(1) | m_H(32) | ts_2(1) = 34 B
 *   g. Forward to GW:   new_PID(32) | ID_AS(1) | enc_token(48) = 81 B
 * ========================================================================== */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "contiki.h"
#include "coap-engine.h"
#include "coap-blocking-api.h"
#include "aes.h"
#include "sha256.h"
#include "random.h"
#include "sys/node-id.h"
#include "net/ipv6/uip-ds6.h"
#include "project-conf.h"
#include "sys/energest.h"

/* --------------------------------------------------------------------------
 * Shared long-term symmetric keys — EXACTLY 16 bytes each.
 * -------------------------------------------------------------------------- */
static const uint8_t K_AS_D[16]  = {
    0x67,0x61,0x74,0x73,0x20,0x6D,0x79,0x20,
    0x4B,0x75,0x6F,0x67,0x20,0x46,0x75,0x00
};
static const uint8_t K_GW_AS[16] = {
    0x67,0x62,0x74,0x73,0x20,0x6D,0x79,0x20,
    0x4B,0x75,0x6F,0x67,0x20,0x46,0x75,0x00
};

/* --------------------------------------------------------------------------
 * Packet sizes
 *   REG0_REQ  = 16  (1 AES block: id_d + pad)
 *   REG0_REP  = 48  (3 AES blocks: c_d + m_d[32] + pad)
 *   REG1_REQ  = 48  (3 AES blocks: id_d + y_dH[32] + R_d + c_as_d + pad)
 *   AUTH_REQ  = 65  (plain: PID[32] + y_asd[32] + ts_1)
 *   AUTH_REP  = 34  (plain: ACK + m_H[32] + ts_2)
 *   GW_TOKEN  = 81  (plain PID[32] + ID_AS + enc_block×3[48])
 * -------------------------------------------------------------------------- */
#define REG0_REQ_LEN   16
#define REG0_REP_LEN   48
#define REG1_REQ_LEN   48
#define AUTH_REQ_LEN   65
#define AUTH_REP_LEN   34
#define GW_TOKEN_LEN   81
#define ACK_BYTE       0xAC

#define MAX_CLIENTS    110

/* --------------------------------------------------------------------------
 * Global AND-accumulator.
 * Initialised to 0xFF…FF.  Each enrolled device ANDs its y_dH in.
 * Membership test: (T_acc & y_dH) == T_acc
 * -------------------------------------------------------------------------- */
static uint8_t T_acc[32];
static uint8_t session_ctr = 0; /* monotone counter used as ts_2 */

/* --------------------------------------------------------------------------
 * Per-client state
 * -------------------------------------------------------------------------- */
typedef struct {
    uint8_t  ID_d;
    uint8_t  c_d;             /* PUF challenge AS issued to device           */
    uint8_t  c_as_d;          /* PUF challenge device issued to AS           */
    uint8_t  phi_as_d;        /* R_as XOR R_d  (PUF binding value)           */
    uint8_t  PID_curr[32];    /* H(ID || m_curr)  current pseudonym          */
    uint8_t  PID_old[32];     /* H(ID || m_old)   previous pseudonym (desync)*/
    uint8_t  m_curr[32];      /* current session-based random                */
    uint8_t  m_old[32];       /* previous session-based random (desync)      */
    uint8_t  last_ts1;        /* last accepted ts_1 for replay prevention    */
    uint8_t  enrolled;        /* 1 after Reg-1 completes                     */
    uint8_t  pid_old_valid;   /* 1 once first pseudonym rotation has happened*/
} client_t;

static client_t clients[MAX_CLIENTS];

/* --------------------------------------------------------------------------
 * Token ring-buffer (head chases tail)
 * -------------------------------------------------------------------------- */
static uint8_t  tok_buf[MAX_CLIENTS][GW_TOKEN_LEN];
static uint8_t  tok_head = 0;   /* next slot to read (send to GW)  */
static uint8_t  tok_tail = 0;   /* next slot to write              */
#define TOK_EMPTY()  (tok_head == tok_tail)
#define TOK_FULL()   (((tok_tail + 1) % MAX_CLIENTS) == tok_head)

/* Energest — cumulative at auth time, same as coap-server.c */
#define CURRENT_CPU     1.8e-3
#define CURRENT_LPM     0.0545e-3
#define CURRENT_TX      17.4e-3
#define CURRENT_RX      18.8e-3
#define SUPPLY_VOLTAGE  3.0

static double cpu_auth_as, energy_auth_as;

static void print_energest_stats(double *seconds_cpu, double *total_energy) {
  energest_flush();

  unsigned long cpu_ticks = energest_type_time(ENERGEST_TYPE_CPU);
  unsigned long lpm_ticks = energest_type_time(ENERGEST_TYPE_LPM);
  unsigned long tx_ticks  = energest_type_time(ENERGEST_TYPE_TRANSMIT);
  unsigned long rx_ticks  = energest_type_time(ENERGEST_TYPE_LISTEN);

  *seconds_cpu = cpu_ticks / (double)ENERGEST_SECOND;
  double seconds_lpm = lpm_ticks / (double)ENERGEST_SECOND;
  double seconds_tx  = tx_ticks  / (double)ENERGEST_SECOND;
  double seconds_rx  = rx_ticks  / (double)ENERGEST_SECOND;

  double energy_cpu = *seconds_cpu * CURRENT_CPU * SUPPLY_VOLTAGE;
  double energy_lpm = seconds_lpm * CURRENT_LPM * SUPPLY_VOLTAGE;
  double energy_tx  = seconds_tx  * CURRENT_TX  * SUPPLY_VOLTAGE;
  double energy_rx  = seconds_rx  * CURRENT_RX  * SUPPLY_VOLTAGE;

  *total_energy = energy_cpu + energy_lpm + energy_tx + energy_rx;
}

static coap_endpoint_t  ep_gw;
static coap_message_t   req_gw[1];
process_event_t         ev_send_tok;
PROCESS_NAME(as_proc);

/* ==========================================================================
 * Utility helpers
 * ========================================================================== */

/* Deterministic per-device PUF simulation.
 * Same node_id + same challenge always returns the same byte.              */
static uint8_t puf_response(uint8_t challenge)
{
    uint32_t s = ((uint32_t)node_id  * 2246822519UL)
               ^ ((uint32_t)challenge * 2654435761UL);
    s = ((s >> 16) ^ s) * 0x45d9f3bUL;
    s = ((s >> 16) ^ s) * 0x45d9f3bUL;
    s ^= (s >> 16);
    return (uint8_t)(s & 0xFF);
}

/* Generate len pseudo-random bytes (good enough for simulation).           */
static void gen_random(uint8_t *buf, uint8_t len)
{
    for (uint8_t i = 0; i < len; i++) {
        uint16_t r = random_rand();
        buf[i] = (uint8_t)((r & 0xFF) ^ (uint8_t)(clock_time() >> (i & 7)));
    }
}

/* SHA-256 one-shot wrapper.                                                */
static void H(const uint8_t *in, uint16_t len, uint8_t *out)
{
    SHA256_CTX ctx;
    sha256_init(&ctx);
    sha256_update(&ctx, in, len);
    sha256_final(&ctx, out);
}

/* AES-ECB encrypt / decrypt n consecutive 16-byte blocks in-place.        */
static void aes_enc(const uint8_t *key, uint8_t *buf, uint8_t n)
{
    struct AES_ctx ctx;
    for (uint8_t i = 0; i < n; i++) {
        AES_init_ctx(&ctx, key);
        AES_ECB_encrypt(&ctx, buf + i * 16);
    }
}
static void aes_dec(const uint8_t *key, uint8_t *buf, uint8_t n)
{
    struct AES_ctx ctx;
    for (uint8_t i = 0; i < n; i++) {
        AES_init_ctx(&ctx, key);
        AES_ECB_decrypt(&ctx, buf + i * 16);
    }
}

/* ts_1 freshness: new_ts must be strictly ahead of last_ts in a uint8
 * counter sense (handles wraparound; max window = 200 steps).             */
static int seq_ts_fresh(uint8_t new_ts, uint8_t last_ts)
{
    int diff = ((int)new_ts - (int)last_ts + 256) % 256;
    return (diff > 0 && diff <= 200);
}

/* IPv6 address construction for GW.                                       */
static void discover_gw(void)
{
    uip_ipaddr_t a;
    uint8_t g = GW_NODE_ID;
    uip_ip6addr_u8(&a, 0xfd,0,0,0,0,0,0,0, 0x02,g,0,g,0,g,0,g);
    uip_ipaddr_copy(&ep_gw.ipaddr, &a);
    ep_gw.port = UIP_HTONS(COAP_DEFAULT_PORT);
}

/* ==========================================================================
 * PHASE 1a — Enrollment Step 0 (GET /test/reg)
 *
 * Receive: AES_enc(K_AS_D, [id_d | pad×15]) = 16 B
 * Reply:   AES_enc(K_AS_D, [c_d | m_d[0..14]]) ||
 *          AES_enc(K_AS_D, [m_d[15..30]])        ||
 *          AES_enc(K_AS_D, [m_d[31] | pad×15])   = 48 B
 *
 * AS generates fresh random c_d AND fresh random m_d for this device and
 * sends them over the assumed secure channel (encrypted with K_AS_D).
 * ========================================================================== */
static void res_reg_handler(coap_message_t *req, coap_message_t *resp,
                            uint8_t *buf, uint16_t ps, int32_t *off)
{
    const uint8_t *chunk;
    if (coap_get_payload(req, &chunk) != REG0_REQ_LEN) return;

    /* Decrypt and extract device ID */
    uint8_t plain[16];
    memcpy(plain, chunk, 16);
    aes_dec(K_AS_D, plain, 1);
    uint8_t id_d = plain[0];
    if (id_d == 0 || id_d >= MAX_CLIENTS) return;

    /* Initialise / reset client slot */
    clients[id_d].ID_d          = id_d;
    clients[id_d].enrolled      = 0;
    clients[id_d].pid_old_valid = 0;
    clients[id_d].last_ts1      = 0;

    /* Generate fresh random c_d (1 byte) and m_d (32 bytes) */
    clients[id_d].c_d = (uint8_t)(random_rand() & 0xFF);
    gen_random(clients[id_d].m_curr, 32);
    /* m_old mirrors m_curr at enrolment (nothing to fall back to yet) */
    memcpy(clients[id_d].m_old, clients[id_d].m_curr, 32);

    /* Pack reply: byte[0] = c_d, bytes[1..32] = m_d, bytes[33..47] = 0 */
    uint8_t reply[REG0_REP_LEN];
    memset(reply, 0, REG0_REP_LEN);
    reply[0] = clients[id_d].c_d;
    memcpy(reply + 1, clients[id_d].m_curr, 32);
    aes_enc(K_AS_D, reply, 3);   /* encrypt 3 × 16 B blocks */

    coap_set_payload(resp, reply, REG0_REP_LEN);

    printf("AS %u: Reg-0 for device %u (c_d=%u)\n",
           node_id, id_d, clients[id_d].c_d);
}

/* ==========================================================================
 * PHASE 1b — Enrollment Step 1 (POST /test/reg1)
 *
 * Receive: AES_enc(K_AS_D, [id_d | y_dH[0..14]])  ||
 *          AES_enc(K_AS_D, [y_dH[15..30]])          ||
 *          AES_enc(K_AS_D, [y_dH[31] | R_d | c_as_d | pad×13]) = 48 B
 *
 * AS actions (per spec):
 *   T_acc   = T_acc & y_dH
 *   R_as    = PUF(c_as_d)
 *   phi_as  = R_as XOR R_d
 *   PID_curr = H(ID || m_curr);  PID_old = not valid yet
 * ========================================================================== */
static void res_reg1_handler(coap_message_t *req, coap_message_t *resp,
                             uint8_t *buf, uint16_t ps, int32_t *off)
{
    const uint8_t *chunk;
    if (coap_get_payload(req, &chunk) != REG1_REQ_LEN) return;

    /* Decrypt 3 blocks */
    uint8_t plain[REG1_REQ_LEN];
    memcpy(plain, chunk, REG1_REQ_LEN);
    aes_dec(K_AS_D, plain, 3);

    uint8_t id_d   = plain[0];
    if (id_d == 0 || id_d >= MAX_CLIENTS || clients[id_d].ID_d != id_d) return;

    uint8_t Y_dH[32];
    memcpy(Y_dH, plain + 1, 32);       /* bytes  1..32 : y_dH   */
    uint8_t R_d    = plain[33];        /* byte  33     : R_d    */
    uint8_t c_as_d = plain[34];        /* byte  34     : c_as_d */

    clients[id_d].c_as_d = c_as_d;

    /* T_acc = T_acc & y_dH  (AND accumulator update, per spec) */
    for (int i = 0; i < 32; i++) T_acc[i] &= Y_dH[i];

    /* R_as = PUF(c_as_d) on the AS node */
    uint8_t R_as = puf_response(c_as_d);

    /* phi_as_d = R_as XOR R_d */
    clients[id_d].phi_as_d = R_as ^ R_d;

    /* PID_curr = H(ID || m_curr) — initial pseudonym */
    uint8_t pid_in[33];
    pid_in[0] = id_d;
    memcpy(pid_in + 1, clients[id_d].m_curr, 32);
    H(pid_in, 33, clients[id_d].PID_curr);

    /* PID_old is not valid yet */
    memset(clients[id_d].PID_old, 0, 32);
    clients[id_d].pid_old_valid = 0;
    clients[id_d].enrolled      = 1;

    const char *msg = "Registered";
    coap_set_payload(resp, (const uint8_t *)msg, strlen(msg));

    printf("AS %u: Reg-1 complete for device %u\n",
           node_id, id_d);
}

/* ==========================================================================
 * PHASE 2 + 3 — Authentication & Key Exchange (POST /test/auth)
 *
 * Receive: PID(32) | y_asd(32) | ts_1(1) = 65 B  (sent in plain)
 *
 * Phase 2 steps:
 *   a. Search PID_curr / PID_old.
 *   b. Freshness check on ts_1 (sequence-based).
 *   c. R_as = PUF(c_as_d);  R_d = phi_as_d XOR R_as
 *   d. mask = H(R_d || m_active || PID || ts_1)
 *      y_dH = y_asd XOR mask
 *   e. T_new = T_acc & y_dH;  accept iff T_new == T_acc
 *
 * Phase 3 steps:
 *   a. n1 = rand(32);  ts_2 = clock;  m_new = H(n1)
 *   b. mH_mask = H(y_dH || m_active || R_d || ID_AS || PID || ts_2)
 *      m_H = m_new XOR mH_mask
 *   c. K_GW_D = H(R_d || m_new)
 *   d. ts_auth = clock
 *      Build enc_token (48 B) = AES_enc(K_GW_AS, 3 blocks)
 *   e. Rotate: PID_old=PID_curr; PID_curr=H(ID||m_new)
 *              m_old=m_curr;     m_curr=m_new
 *   f. Reply to device: ACK(1) | m_H(32) | ts_2(1) = 34 B
 *   g. Enqueue to GW:   new_PID(32) | ID_AS(1) | enc_token(48) = 81 B
 * ========================================================================== */
static void res_auth_handler(coap_message_t *req, coap_message_t *resp,
                             uint8_t *buf, uint16_t ps, int32_t *off)
{
    const uint8_t *chunk;
    int len = coap_get_payload(req, &chunk);
    if (len < AUTH_REQ_LEN) {
        printf("AS %u: Auth packet too short (%d B)\n", node_id, len);
        return;
    }

    uint8_t recv_PID[32], y_asd[32], ts_1;
    memcpy(recv_PID, chunk,      32);
    memcpy(y_asd,    chunk + 32, 32);
    ts_1 = chunk[64];

    /* ------------------------------------------------------------------
     * Phase 2a: Find client by PID (current first, then old for desync)
     * ------------------------------------------------------------------ */
    int     found   = -1;
    uint8_t use_old = 0;
    for (int i = 1; i < MAX_CLIENTS; i++) {
        if (!clients[i].enrolled) continue;
        if (memcmp(clients[i].PID_curr, recv_PID, 32) == 0) {
            found = i; use_old = 0; break;
        }
        if (clients[i].pid_old_valid &&
            memcmp(clients[i].PID_old, recv_PID, 32) == 0) {
            found = i; use_old = 1; break;
        }
    }
    if (found == -1) {
        printf("AS %u: Auth failed — PID not found\n", node_id);
        return;
    }
    if (use_old)
        printf("AS %u: Desync recovery for device %u (matched PID_old)\n",
               node_id, found);

    client_t *cl       = &clients[found];
    uint8_t  *m_active = use_old ? cl->m_old : cl->m_curr;

    /* ------------------------------------------------------------------
     * Phase 2b: Freshness check — ts_1 must be strictly ahead of last
     * ------------------------------------------------------------------ */
    /* In normal flow: ts_1 must be strictly ahead.
     * In desync recovery (use_old): device rejected our last reply and never
     * advanced ts_1, so we accept ts_1 == last_ts1 to break the deadlock.  */
    if (use_old) {
        /* allow equal — device is replaying the same ts_1 it already sent */
        int diff = ((int)ts_1 - (int)cl->last_ts1 + 256) % 256;
        if (diff > 200) {
            printf("AS %u: Auth failed — ts_1 wrapped badly in desync for device %u\n",
                   node_id, found);
            return;
        }
    } else {
        if (!seq_ts_fresh(ts_1, cl->last_ts1)) {
            printf("AS %u: Auth failed — stale ts_1 for device %u\n",
                   node_id, found);
            return;
        }
    }

    /* ------------------------------------------------------------------
     * Phase 2c: Recover R_d
     *   R_as = PUF(c_as_d)  [AS-side PUF, deterministic]
     *   R_d  = phi_as_d XOR R_as
     * ------------------------------------------------------------------ */
    uint8_t R_as = puf_response(cl->c_as_d);
    uint8_t R_d  = cl->phi_as_d ^ R_as;

    /* ------------------------------------------------------------------
     * Phase 2d: Recover y_dH
     *   mask = H(R_d || m_active || PID || ts_1)   [66 bytes input]
     *   y_dH = y_asd XOR mask
     * ------------------------------------------------------------------ */
    uint8_t mask_in[66], mask[32], Y_dH[32];
    mask_in[0] = R_d;
    memcpy(mask_in + 1,  m_active, 32);
    memcpy(mask_in + 33, recv_PID, 32);
    mask_in[65] = ts_1;
    H(mask_in, 66, mask);
    for (int i = 0; i < 32; i++) Y_dH[i] = y_asd[i] ^ mask[i];

    /* ------------------------------------------------------------------
     * Phase 2e: Membership test
     *   T_new = T_acc & y_dH
     *   Accept iff T_new == T_acc
     * ------------------------------------------------------------------ */
    uint8_t T_new[32];
    for (int i = 0; i < 32; i++) T_new[i] = T_acc[i] & Y_dH[i];
    if (memcmp(T_new, T_acc, 32) != 0) {
        printf("AS %u: Auth failed — membership check failed (device %u)\n",
               node_id, found);
        return;
    }

    /* Device is authenticated */
    cl->last_ts1 = ts_1;
    printf("AS %u: Device %u authenticated (membership check passed)\n",
           node_id, found);

    /* ==================================================================
     * Phase 3 — Key Exchange
     * ================================================================== */

    /* 3a: Generate random n1 (32 B), ts_2 = clock, m_new = H(n1) */
    uint8_t n1[32], m_new[32];
    gen_random(n1, 32);
    H(n1, 32, m_new);
    uint8_t ts_2 = ++session_ctr;  /* sequential counter — no clock-boundary issues */

    /* 3b: Compute m_H
     *   mH_mask = H(y_dH || m_active || R_d || ID_AS || PID || ts_2)
     *             [input = 32+32+1+1+32+1 = 99 bytes]
     *   m_H = m_new XOR mH_mask
     * ------------------------------------------------------------------ */
    uint8_t mh_in[99], mh_mask[32], m_H[32];
    memcpy(mh_in,      Y_dH,      32);   /* bytes  0..31  y_dH    */
    memcpy(mh_in + 32, m_active,  32);   /* bytes 32..63  m_d     */
    mh_in[64] = R_d;                     /* byte  64      R_d     */
    mh_in[65] = (uint8_t)node_id;        /* byte  65      ID_AS   */
    memcpy(mh_in + 66, recv_PID,  32);   /* bytes 66..97  PID     */
    mh_in[98] = ts_2;                    /* byte  98      ts_2    */
    H(mh_in, 99, mh_mask);
    for (int i = 0; i < 32; i++) m_H[i] = m_new[i] ^ mh_mask[i];

    /* 3c: K_GW_D = H(R_d || m_new)  [33 bytes input] */
    uint8_t kd_in[33], K_GW_D[32];
    kd_in[0] = R_d;
    memcpy(kd_in + 1, m_new, 32);
    H(kd_in, 33, K_GW_D);

    /* 3d: Build encrypted auth token for GW
     *   SE(K_GW_AS, ID_d | ID_AS | ts_auth | pad(13))  — Block A
     *   SE(K_GW_AS, K_GW_D[0..15])                     — Block B
     *   SE(K_GW_AS, K_GW_D[16..31])                    — Block C
     *   Total encrypted = 48 B
     * ------------------------------------------------------------------ */
    uint8_t ts_auth = (uint8_t)(clock_time() / CLOCK_SECOND);
    uint8_t enc_tok[48];
    memset(enc_tok, 0, 48);
    enc_tok[0] = (uint8_t)found;       /* ID_d   — Block A byte 0 */
    enc_tok[1] = (uint8_t)node_id;     /* ID_AS  — Block A byte 1 */
    enc_tok[2] = ts_auth;              /* ts_auth— Block A byte 2 */
    memcpy(enc_tok + 16, K_GW_D,      16);  /* Block B */
    memcpy(enc_tok + 32, K_GW_D + 16, 16); /* Block C */
    aes_enc(K_GW_AS, enc_tok, 3);

    /* 3e: Pseudonym rotation
     *   PID_old  = PID_curr       m_old  = m_curr
     *   PID_curr = H(ID||m_new)   m_curr = m_new
     * ------------------------------------------------------------------ */
    memcpy(cl->PID_old, cl->PID_curr, 32);
    memcpy(cl->m_old,   cl->m_curr,   32);
    cl->pid_old_valid = 1;

    uint8_t new_pid_in[33];
    new_pid_in[0] = (uint8_t)found;
    memcpy(new_pid_in + 1, m_new, 32);
    H(new_pid_in, 33, cl->PID_curr);
    memcpy(cl->m_curr, m_new, 32);

    /* 3f: Reply to device: ACK(1) | m_H(32) | ts_2(1) = 34 B */
    uint8_t reply[AUTH_REP_LEN];
    reply[0] = ACK_BYTE;
    memcpy(reply + 1, m_H, 32);
    reply[33] = ts_2;
    coap_set_payload(resp, reply, AUTH_REP_LEN);

    /* 3g: Enqueue token for GW
     *   Layout: new_PID(32) | ID_AS(1) | enc_tok(48) = 81 B
     *   new_PID = cl->PID_curr  (already updated to H(ID||m_new) above)
     * ------------------------------------------------------------------ */
    if (!TOK_FULL()) {
        uint8_t *slot = tok_buf[tok_tail];
        memcpy(slot,      cl->PID_curr, 32);     /* new PID after rotation */
        slot[32] = (uint8_t)node_id;              /* ID_AS                  */
        memcpy(slot + 33, enc_tok,      48);      /* encrypted token        */
        tok_tail = (tok_tail + 1) % MAX_CLIENTS;
        process_post(&as_proc, ev_send_tok, NULL);
    } else {
        printf("AS %u: Token queue full — dropping token for device %u\n",
               node_id, found);
    }

    /* Cumulative energest at auth time — same as coap-server.c */
    print_energest_stats(&cpu_auth_as, &energy_auth_as);
    printf("\n The CPU time and energy at the end of authentication for server %u are %f and %f",
           node_id, cpu_auth_as, energy_auth_as);
}

/* --------------------------------------------------------------------------
 * CoAP resource declarations
 *   res_reg  → GET  (device uses COAP_GET for small 16-byte payload)
 *   res_reg1 → POST (device sends 48-byte encrypted body)
 *   res_auth → POST (device sends 65-byte auth request)
 * -------------------------------------------------------------------------- */
RESOURCE(res_reg,  "title=\"Reg\"",  res_reg_handler,  NULL, NULL, NULL);
RESOURCE(res_reg1, "title=\"Reg1\"", NULL, res_reg1_handler, NULL, NULL);
RESOURCE(res_auth, "title=\"Auth\"", NULL, res_auth_handler, NULL, NULL);

/* Callback for GW ACK on token delivery */
static void gw_tok_ack(coap_message_t *resp)
{
    if (!resp)
        printf("AS %u: Token delivery to GW timed out\n", node_id);
    /* Advance head regardless to avoid stalling the queue */
    tok_head = (tok_head + 1) % MAX_CLIENTS;
}

/* ==========================================================================
 * Main process
 * ========================================================================== */
PROCESS(as_proc, "AS");
AUTOSTART_PROCESSES(&as_proc);

PROCESS_THREAD(as_proc, ev, data)
{
    PROCESS_BEGIN();

    memset(clients, 0, sizeof(clients));
    memset(T_acc, 0xFF, 32);   /* AND accumulator starts all-ones */
    tok_head = tok_tail = 0;
    session_ctr = 0;

    coap_engine_init();
    discover_gw();

    coap_activate_resource(&res_reg,  "test/reg");
    coap_activate_resource(&res_reg1, "test/reg1");
    coap_activate_resource(&res_auth, "test/auth");

    ev_send_tok = process_alloc_event();
    printf("AS %u: Started.\n", node_id);

    while (1) {
        PROCESS_WAIT_EVENT_UNTIL(ev == ev_send_tok);
        /* Drain the queue: deliver every pending token to the GW */
        while (!TOK_EMPTY()) {
            uint8_t payload[GW_TOKEN_LEN];
            memcpy(payload, tok_buf[tok_head], GW_TOKEN_LEN);
            coap_init_message(req_gw, COAP_TYPE_CON, COAP_POST, coap_get_mid());
            coap_set_header_uri_path(req_gw, "test/auth_token");
            coap_set_payload(req_gw, payload, GW_TOKEN_LEN);
            COAP_BLOCKING_REQUEST(&ep_gw, req_gw, gw_tok_ack);
            /* gw_tok_ack advances tok_head after each delivery */
        }
    }

    PROCESS_END();
}
