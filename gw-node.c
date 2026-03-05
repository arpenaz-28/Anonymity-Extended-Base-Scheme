/* ==========================================================================
 * gw-node.c  —  Gateway Node (RPL root + CoAP server)
 *
 * Receives an auth token from the AS and a data packet from the device.
 *
 * TOKEN from AS (POST /test/auth_token): 81 bytes
 *   new_PID(32) | ID_AS(1) | enc_A(16) | enc_B(16) | enc_C(16)
 *   enc_A = AES_enc(K_GW_AS, [ID_d | ID_AS | ts_auth | pad(13)])
 *   enc_B = AES_enc(K_GW_AS, K_GW_D[0..15])
 *   enc_C = AES_enc(K_GW_AS, K_GW_D[16..31])
 *
 *   GW actions:
 *     Decrypt A, B, C.
 *     Check freshness of ts_auth (clock-based).
 *     Store session keyed by new_PID:
 *       { PID, ID_d, ID_AS, K_GW_D[32], ts_auth }
 *
 * DATA from device (POST /test/data): 48 bytes
 *   new_PID(32) | AES_enc(K_GW_D[0..15], data(16))
 *
 *   GW actions:
 *     Look up session by PID.
 *     Decrypt data.
 *     Print plaintext value.
 *
 * KEY DESIGN POINT: the GW stores and looks up by PID, not by node ID.
 * This means the GW treats devices as pseudonymous entities.  It learns
 * the real ID only from the decrypted token interior (for logging), but
 * the external lookup key is always the rotating PID.
 * ========================================================================== */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "contiki.h"
#include "coap-engine.h"
#include "aes.h"
#include "net/routing/routing.h"
#include "net/netstack.h"
#include "sys/node-id.h"
#include "project-conf.h"

/* --------------------------------------------------------------------------
 * Shared long-term key — EXACTLY 16 bytes.
 * -------------------------------------------------------------------------- */
static const uint8_t K_GW_AS[16] = {
    0x67,0x62,0x74,0x73,0x20,0x6D,0x79,0x20,
    0x4B,0x75,0x6F,0x67,0x20,0x46,0x75,0x00
};

/* --------------------------------------------------------------------------
 * Session table (indexed by slot, looked up by PID)
 * -------------------------------------------------------------------------- */
#define MAX_SESSIONS  110

typedef struct {
    uint8_t  PID[32];      /* pseudonym — external lookup key             */
    uint8_t  ID_d;         /* real device ID (from decrypted token)       */
    uint8_t  ID_as;        /* which AS authenticated this device          */
    uint8_t  K_GW_D[32];   /* 32-byte session key                         */
    uint8_t  ts_auth;      /* token freshness timestamp                   */
    uint8_t  valid;        /* 1 = slot in use                             */
} gw_session_t;

static gw_session_t sessions[MAX_SESSIONS];

/* Linear PID search */
static gw_session_t *find_by_pid(const uint8_t *pid)
{
    for (int i = 0; i < MAX_SESSIONS; i++) {
        if (sessions[i].valid && memcmp(sessions[i].PID, pid, 32) == 0)
            return &sessions[i];
    }
    return NULL;
}

/* Allocate a free slot (or overwrite the first slot if all full) */
static gw_session_t *alloc_session(void)
{
    for (int i = 0; i < MAX_SESSIONS; i++) {
        if (!sessions[i].valid) return &sessions[i];
    }
    printf("GW: Session table full — overwriting slot 0\n");
    return &sessions[0];
}

/* --------------------------------------------------------------------------
 * AES-ECB decrypt n consecutive 16-byte blocks in-place.
 * -------------------------------------------------------------------------- */
static void aes_dec(const uint8_t *key, uint8_t *buf, uint8_t n)
{
    struct AES_ctx ctx;
    for (uint8_t i = 0; i < n; i++) {
        AES_init_ctx(&ctx, key);
        AES_ECB_decrypt(&ctx, buf + i * 16);
    }
}

/* --------------------------------------------------------------------------
 * Clock-based freshness check (uint8 wraparound safe).
 * -------------------------------------------------------------------------- */
static int ts_fresh(uint8_t recv_ts)
{
    uint8_t now  = (uint8_t)(clock_time() / CLOCK_SECOND);
    int     diff = ((int)now - (int)recv_ts + 256) % 256;
    return (diff < FRESHNESS_WINDOW);
}

/* ==========================================================================
 * Resource: receive auth token from AS
 * POST /test/auth_token
 * Payload: new_PID(32) | ID_AS(1) | enc_A(16) | enc_B(16) | enc_C(16) = 81 B
 * ========================================================================== */
static void res_authtoken_handler(coap_message_t *req, coap_message_t *resp,
                                  uint8_t *buf, uint16_t ps, int32_t *off)
{
    const uint8_t *chunk;
    if (coap_get_payload(req, &chunk) != 81) {
        printf("GW: Token wrong length\n");
        return;
    }

    clock_time_t t_start = clock_time();

    /* Parse packet layout */
    uint8_t new_PID[32];
    uint8_t id_as_plain;
    uint8_t enc_tok[48];

    memcpy(new_PID,   chunk,      32);
    id_as_plain = chunk[32];
    memcpy(enc_tok,   chunk + 33, 48);

    /* Decrypt three blocks with K_GW_AS */
    aes_dec(K_GW_AS, enc_tok, 3);

    /* Block A: ID_d(byte 0) | ID_AS(byte 1) | ts_auth(byte 2) | pad(13) */
    uint8_t id_d    = enc_tok[0];
    uint8_t id_as   = enc_tok[1];
    uint8_t ts_auth = enc_tok[2];

    /* Block B + C: K_GW_D (32 bytes) */
    uint8_t K_GW_D[32];
    memcpy(K_GW_D,      enc_tok + 16, 16);
    memcpy(K_GW_D + 16, enc_tok + 32, 16);

    /* Sanity: ID_AS in plaintext header must match decrypted value */
    if (id_as != id_as_plain) {
        printf("GW: Token rejected — ID_AS mismatch\n");
        return;
    }

    /* Freshness check on ts_auth */
    if (!ts_fresh(ts_auth)) {
        printf("GW: Token rejected — stale ts_auth for device %u\n", id_d);
        return;
    }

    /* If a session with this PID already exists, refresh it.
     * Otherwise allocate a new slot.                                       */
    gw_session_t *sess = find_by_pid(new_PID);
    if (!sess) sess = alloc_session();

    memcpy(sess->PID,    new_PID, 32);
    sess->ID_d    = id_d;
    sess->ID_as   = id_as;
    sess->ts_auth = ts_auth;
    sess->valid   = 1;
    memcpy(sess->K_GW_D, K_GW_D, 32);

    printf("GW: Auth token for device %u (via AS %u). "
           "PID: %02x%02x%02x... stored.\n",
           id_d, id_as, new_PID[0], new_PID[1], new_PID[2]);

    {
        unsigned long proc_ms = (unsigned long)(
            (clock_time() - t_start) * 1000UL / CLOCK_SECOND);
        printf("GW: Token processing time: %lu ms\n", proc_ms);
    }

    const char *msg = "OK";
    coap_set_payload(resp, (const uint8_t *)msg, strlen(msg));
}

/* ==========================================================================
 * Resource: receive encrypted sensor data from authenticated device
 * POST /test/data
 * Payload: new_PID(32) | AES_enc(K_GW_D[0..15], data(16)) = 48 B
 * ========================================================================== */
static void res_data_handler(coap_message_t *req, coap_message_t *resp,
                             uint8_t *buf, uint16_t ps, int32_t *off)
{
    const uint8_t *chunk;
    if (coap_get_payload(req, &chunk) < 48) return;

    clock_time_t t_start = clock_time();

    uint8_t recv_PID[32], enc_data[16];
    memcpy(recv_PID,  chunk,      32);
    memcpy(enc_data,  chunk + 32, 16);

    /* Look up session by PID */
    gw_session_t *sess = find_by_pid(recv_PID);
    if (!sess) {
        printf("GW: Rejected data — PID %02x%02x%02x... not found\n",
               recv_PID[0], recv_PID[1], recv_PID[2]);
        return;
    }

    /* Decrypt using first 16 bytes of K_GW_D (AES-128 key) */
    struct AES_ctx ctx;
    uint8_t K_AES[16];
    memcpy(K_AES, sess->K_GW_D, 16);
    AES_init_ctx(&ctx, K_AES);
    AES_ECB_decrypt(&ctx, enc_data);

    printf("GW: Decrypted data [%u] from PID %02x%02x%02x... (device %u)\n",
           enc_data[0], recv_PID[0], recv_PID[1], recv_PID[2], sess->ID_d);

    {
        unsigned long proc_ms = (unsigned long)(
            (clock_time() - t_start) * 1000UL / CLOCK_SECOND);
        printf("GW: Data processing time: %lu ms\n", proc_ms);
    }

    uint8_t reply[1] = {0};
    coap_set_payload(resp, reply, 1);
}

/* --------------------------------------------------------------------------
 * CoAP resource declarations (both on POST slot)
 * -------------------------------------------------------------------------- */
RESOURCE(res_authtoken, "title=\"AuthToken\"",
         NULL, res_authtoken_handler, NULL, NULL);
RESOURCE(res_data,      "title=\"Data\"",
         NULL, res_data_handler,      NULL, NULL);

/* ==========================================================================
 * Main process
 * ========================================================================== */
PROCESS(gw_node, "Gateway Node");
AUTOSTART_PROCESSES(&gw_node);

PROCESS_THREAD(gw_node, ev, data)
{
    PROCESS_BEGIN();

    memset(sessions, 0, sizeof(sessions));

    /* Become the RPL root (DAG root) */
    NETSTACK_ROUTING.root_start();

    /* Initialise CoAP engine — REQUIRED to service incoming requests */
    coap_engine_init();

    coap_activate_resource(&res_authtoken, "test/auth_token");
    coap_activate_resource(&res_data,      "test/data");

    printf("GW %u: Started (RPL root + CoAP server).\n", node_id);
    printf("GW %u: Storage: %u bytes (%d sessions x %u bytes each)\n",
           node_id, (unsigned)sizeof(sessions),
           MAX_SESSIONS, (unsigned)sizeof(gw_session_t));

    while (1) {
        PROCESS_WAIT_EVENT();
    }

    PROCESS_END();
}
