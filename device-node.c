/* ==========================================================================
 * device-node.c  —  IoT Device Node  (PUF-based revised scheme)
 *
 * Measurement methodology mirrors base scheme (coap-client.c) EXACTLY:
 *
 *  Timer stagger  : etimer_set(&et, CLOCK_SECOND * (5 + node_id))
 *  Loop guard     : if (etimer_expired(&et))
 *  Timer reset    : etimer_reset(&et)
 *
 *  State machine:
 *    reg == 0  → Enrollment   : Reg-0 COAP + Reg-1 COAP  (single timer tick)
 *    reg == 1,
 *    count < 1 → Auth+Data    : [BEFORE]
 *                               Auth COAP  (our scheme: includes key exchange)
 *                               Data COAP
 *                               count++
 *                               [AFTER on count==1]
 *                               print (cpu_auth - cpu_reg) and (energy_auth - energy_reg)
 *    count >= 1               → keep sending data every tick
 *
 *  Measurement variables (identical names to base scheme):
 *    cpu_reg, energy_reg    — snapshot BEFORE auth+data block
 *    cpu_auth, energy_auth  — snapshot AFTER  auth+data block
 *    Reported: (cpu_auth - cpu_reg) and (energy_auth - energy_reg)
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
#include "net/ipv6/uip-ds6.h"
#include "sys/node-id.h"
#include "random.h"
#include "project-conf.h"
#include "sys/energest.h"

/* --------------------------------------------------------------------------
 * Shared long-term key — EXACTLY 16 bytes (same as base scheme k_as_d)
 * -------------------------------------------------------------------------- */
static const uint8_t K_AS_D[16] = {
    0x67,0x61,0x74,0x73,0x20,0x6D,0x79,0x20,
    0x4B,0x75,0x6F,0x67,0x20,0x46,0x75,0x00
};

/* --------------------------------------------------------------------------
 * Device state
 * -------------------------------------------------------------------------- */
static uint8_t id_d;
static uint8_t id_as;

static uint8_t c_d;
static uint8_t c_as_d = 3;
static uint8_t y_d    = 2;
static uint8_t h_d;
static uint8_t ts_1   = 1;
static uint8_t last_ts2 = 0;

static uint8_t m_d[32];
static uint8_t k_gw_d[32];
static uint8_t PID[32];
static uint8_t auth_PID[32];
static uint8_t auth_Y_dH[32];

/* Base-scheme style state flags */
static uint8_t reg   = 0;   /* 0 = not enrolled yet          */
static uint8_t count = 0;   /* auth+data round counter        */

/* --------------------------------------------------------------------------
 * Energest — IDENTICAL to base scheme (coap-client.c)
 * Variables named exactly as in base scheme for direct comparison.
 * -------------------------------------------------------------------------- */
#define CURRENT_CPU    1.8e-3
#define CURRENT_LPM    0.0545e-3
#define CURRENT_TX     17.4e-3
#define CURRENT_RX     18.8e-3
#define SUPPLY_VOLTAGE 3.0

/* Same variable names as base scheme */
double cpu_reg,    energy_reg;
double cpu_auth,   energy_auth;

/* Enrollment energy snapshots */
double cpu_enroll_before, energy_enroll_before;
double cpu_enroll_after,  energy_enroll_after;

/* Saved durations for metrics summary */
static unsigned long metric_enroll_ms;
static unsigned long metric_auth_ms;
static unsigned long metric_data_ms;

static void print_energest_stats(double *seconds_cpu, double *total_energy)
{
    energest_flush();
    unsigned long cpu_ticks = energest_type_time(ENERGEST_TYPE_CPU);
    unsigned long lpm_ticks = energest_type_time(ENERGEST_TYPE_LPM);
    unsigned long tx_ticks  = energest_type_time(ENERGEST_TYPE_TRANSMIT);
    unsigned long rx_ticks  = energest_type_time(ENERGEST_TYPE_LISTEN);

    *seconds_cpu       = cpu_ticks / (double)ENERGEST_SECOND;
    double seconds_lpm = lpm_ticks / (double)ENERGEST_SECOND;
    double seconds_tx  = tx_ticks  / (double)ENERGEST_SECOND;
    double seconds_rx  = rx_ticks  / (double)ENERGEST_SECOND;

    double energy_cpu = *seconds_cpu * CURRENT_CPU * SUPPLY_VOLTAGE;
    double energy_lpm = seconds_lpm  * CURRENT_LPM * SUPPLY_VOLTAGE;
    double energy_tx  = seconds_tx   * CURRENT_TX  * SUPPLY_VOLTAGE;
    double energy_rx  = seconds_rx   * CURRENT_RX  * SUPPLY_VOLTAGE;

    *total_energy = energy_cpu + energy_lpm + energy_tx + energy_rx;
}

/* --------------------------------------------------------------------------
 * Timing (for manual per-phase calculation from log)
 * -------------------------------------------------------------------------- */
static clock_time_t t_enroll_start;
static clock_time_t t_auth_start;
static clock_time_t t_data_start;

/* --------------------------------------------------------------------------
 * Endpoints
 * -------------------------------------------------------------------------- */
static coap_endpoint_t ep_as, ep_gw;
static coap_message_t  request[1];

/* --------------------------------------------------------------------------
 * Helpers
 * -------------------------------------------------------------------------- */
static uint8_t puf_response(uint8_t challenge)
{
    uint32_t s = ((uint32_t)node_id   * 2246822519UL)
               ^ ((uint32_t)challenge * 2654435761UL);
    s = ((s >> 16) ^ s) * 0x45d9f3bUL;
    s = ((s >> 16) ^ s) * 0x45d9f3bUL;
    s ^= (s >> 16);
    return (uint8_t)(s & 0xFF);
}

static void H(const uint8_t *in, uint16_t len, uint8_t *out)
{
    SHA256_CTX ctx;
    sha256_init(&ctx);
    sha256_update(&ctx, in, len);
    sha256_final(&ctx, out);
}

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

static int ts2_seq_fresh(uint8_t recv, uint8_t last)
{
    int diff = ((int)recv - (int)last + 256) % 256;
    return (diff > 0 && diff <= 200);
}

static void discover_endpoints(void)
{
    uip_ipaddr_t a;
    uint8_t a_id = (uint8_t)AS_NODE_ID;
    uint8_t g_id = (uint8_t)GW_NODE_ID;

    uip_ip6addr_u8(&a, 0xfd,0,0,0,0,0,0,0,
                   0x02,a_id,0,a_id,0,a_id,0,a_id);
    uip_ipaddr_copy(&ep_as.ipaddr, &a);
    ep_as.port = UIP_HTONS(COAP_DEFAULT_PORT);

    uip_ip6addr_u8(&a, 0xfd,0,0,0,0,0,0,0,
                   0x02,g_id,0,g_id,0,g_id,0,g_id);
    uip_ipaddr_copy(&ep_gw.ipaddr, &a);
    ep_gw.port = UIP_HTONS(COAP_DEFAULT_PORT);
}

/* ==========================================================================
 * CoAP response handlers
 * ========================================================================== */

static void client_reg_handler(coap_message_t *resp)
{
    const uint8_t *chunk;
    if (!resp || coap_get_payload(resp, &chunk) < 48) {
        printf("Node %u: Reg-0 dropped\n", id_d);
        return;
    }
    uint8_t plain[48];
    memcpy(plain, chunk, 48);
    aes_dec(K_AS_D, plain, 3);
    c_d = plain[0];
    memcpy(m_d, plain + 1, 32);
    printf("Node %u: Reg-0 OK. c_d=%u\n", id_d, c_d);
}

static void client_reg1_handler(coap_message_t *resp)
{
    if (!resp) {
        printf("Node %u: Reg-1 dropped\n", id_d);
        return;
    }
    unsigned long dur = (unsigned long)(
        (clock_time() - t_enroll_start) * 1000UL / CLOCK_SECOND);
    printf("Node %u: [ENROLLMENT] Duration=%lu ms\n", id_d, dur);
    metric_enroll_ms = dur;
}

static void client_auth_handler(coap_message_t *resp)
{
    const uint8_t *chunk;
    if (!resp || coap_get_payload(resp, &chunk) < 34) {
        printf("Node %u: Auth reply dropped\n", id_d);
        return;
    }

    uint8_t ack  = chunk[0];
    uint8_t m_H[32];
    uint8_t ts_2 = chunk[33];
    memcpy(m_H, chunk + 1, 32);

    if (ack != 0xAC) {
        printf("Node %u: Bad ACK 0x%02x\n", id_d, ack);
        return;
    }
    if (!ts2_seq_fresh(ts_2, last_ts2)) {
        printf("Node %u: Stale ts_2 (%u last=%u)\n", id_d, ts_2, last_ts2);
        return;
    }

    /* Key exchange — device side */
    uint8_t R_d = h_d;
    uint8_t Y_dH[32];
    memcpy(Y_dH, auth_Y_dH, 32);

    uint8_t mh_in[99], mh_mask[32], m_new[32];
    memcpy(mh_in,      Y_dH,     32);
    memcpy(mh_in + 32, m_d,      32);
    mh_in[64] = R_d;
    mh_in[65] = id_as;
    memcpy(mh_in + 66, auth_PID, 32);
    mh_in[98] = ts_2;
    H(mh_in, 99, mh_mask);
    for (int i = 0; i < 32; i++) m_new[i] = m_H[i] ^ mh_mask[i];

    uint8_t kd_in[33];
    kd_in[0] = R_d;
    memcpy(kd_in + 1, m_new, 32);
    H(kd_in, 33, k_gw_d);

    memcpy(m_d, m_new, 32);

    uint8_t pid_buf[33];
    pid_buf[0] = id_d;
    memcpy(pid_buf + 1, m_new, 32);
    H(pid_buf, 33, PID);

    last_ts2 = ts_2;
    ts_1++;

    unsigned long auth_ms = (unsigned long)(
        (clock_time() - t_auth_start) * 1000UL / CLOCK_SECOND);
    printf("Node %u: Auth OK. RTT=%lu ms. New PID=%02x%02x%02x\n",
           id_d, auth_ms, PID[0], PID[1], PID[2]);
    metric_auth_ms = auth_ms;
}

static void client_data_handler(coap_message_t *resp)
{
    if (!resp) {
        printf("Node %u: Data ACK missing\n", id_d);
        return;
    }
    unsigned long data_ms = (unsigned long)(
        (clock_time() - t_data_start) * 1000UL / CLOCK_SECOND);
    printf("Node %u: [DATA] Confirmed. RTT=%lu ms\n", id_d, data_ms);
    metric_data_ms = data_ms;
}

PROCESS(device_node, "Device Node");
AUTOSTART_PROCESSES(&device_node);
static struct etimer et;

/* ==========================================================================
 * Operational cost benchmark (runs once at boot)
 * N_ITER iterations per primitive — same methodology as base paper.
 * ========================================================================== */
#define N_ITER 1000
static void run_benchmark(void)
{
    uint8_t buf[99], out[32], key[16], blk[16];
    uint64_t t0, t1;
    double ms, t_h, t_a, t_p, t_r;
    memset(buf, 0xAB, sizeof(buf));
    memset(key, 0x5C, sizeof(key));
    memset(blk, 0x3D, sizeof(blk));
    printf("\n======== Benchmark (N=%u) ========\n", N_ITER);

    energest_flush();
    t0 = energest_type_time(ENERGEST_TYPE_CPU);
    for (int i = 0; i < N_ITER; i++) H(buf, 99, out);
    energest_flush();
    t1 = energest_type_time(ENERGEST_TYPE_CPU);
    t_h = ms = (t1-t0)*1000.0/ENERGEST_SECOND/N_ITER;
    printf("T_hash : %.4f ms\n", ms);

    energest_flush();
    t0 = energest_type_time(ENERGEST_TYPE_CPU);
    for (int i = 0; i < N_ITER; i++) {
        uint8_t tmp[16]; memcpy(tmp, blk, 16); aes_enc(key, tmp, 1);
    }
    energest_flush();
    t1 = energest_type_time(ENERGEST_TYPE_CPU);
    t_a = ms = (t1-t0)*1000.0/ENERGEST_SECOND/N_ITER;
    printf("T_aes  : %.4f ms\n", ms);

    energest_flush();
    t0 = energest_type_time(ENERGEST_TYPE_CPU);
    for (int i = 0; i < N_ITER; i++) {
        volatile uint8_t r = puf_response((uint8_t)i); (void)r;
    }
    energest_flush();
    t1 = energest_type_time(ENERGEST_TYPE_CPU);
    t_p = ms = (t1-t0)*1000.0/ENERGEST_SECOND/N_ITER;
    printf("T_puf  : %.4f ms\n", ms);

    energest_flush();
    t0 = energest_type_time(ENERGEST_TYPE_CPU);
    for (int i = 0; i < N_ITER; i++) {
        for (int j = 0; j < 32; j++) buf[j] = (uint8_t)random_rand();
    }
    energest_flush();
    t1 = energest_type_time(ENERGEST_TYPE_CPU);
    t_r = ms = (t1-t0)*1000.0/ENERGEST_SECOND/N_ITER;
    printf("T_rand : %.4f ms\n", ms);

    double cost = 2*t_p + 10*t_h + 2*t_a + t_r;
    printf("--- Auth+KE operational cost (device side) ---\n");
    printf("2*T_puf + 10*T_hash + 2*T_aes + T_rand\n");
    printf("= 2*%.4f + 10*%.4f + 2*%.4f + %.4f = %.4f ms\n",
           t_p, t_h, t_a, t_r, cost);
    printf("==========================================\n\n");
}

PROCESS_THREAD(device_node, ev, data)
{
    PROCESS_BEGIN();

    id_d  = (uint8_t)node_id;
    id_as = (uint8_t)AS_NODE_ID;

    discover_endpoints();
    run_benchmark();

    /* Staggered start — IDENTICAL to base scheme:
     * etimer_set(&et, CLOCK_SECOND * (5 + node_id))              */
    etimer_set(&et, CLOCK_SECOND * (5 + node_id));

    while (1) {
        PROCESS_YIELD();

        /* IDENTICAL loop guard to base scheme */
        if (etimer_expired(&et)) {

            /* ============================================================
             * ENROLLMENT — reg == 0
             * Both Reg-0 and Reg-1 in one timer tick (same as base scheme
             * which does both reg COAPs in the reg==0 block).
             * ============================================================ */
            if (reg == 0) {
                /* --- Enrollment energy snapshot (before) --- */
                print_energest_stats(&cpu_enroll_before, &energy_enroll_before);

                /* --- Reg-0 --- */
                uint8_t p0[16];
                memset(p0, 0, 16);
                p0[0] = id_d;
                aes_enc(K_AS_D, p0, 1);

                coap_init_message(request, COAP_TYPE_CON, COAP_GET, 0);
                coap_set_header_uri_path(request, "test/reg");
                coap_set_payload(request, p0, 16);
                t_enroll_start = clock_time();
                printf("Node %u: Sending Reg-0\n", id_d);
                COAP_BLOCKING_REQUEST(&ep_as, request, client_reg_handler);

                /* --- Reg-1 (inline, same tick) --- */
                uint8_t R_d = puf_response(c_d);
                h_d = R_d;

                uint8_t Y_dH[32];
                H(&y_d, 1, Y_dH);

                uint8_t p1[48];
                memset(p1, 0, 48);
                p1[0] = id_d;
                memcpy(p1 + 1, Y_dH, 32);
                p1[33] = R_d;
                p1[34] = c_as_d;
                aes_enc(K_AS_D, p1, 3);

                coap_init_message(request, COAP_TYPE_CON, COAP_POST, 1);
                coap_set_header_uri_path(request, "test/reg1");
                coap_set_payload(request, p1, 48);
                printf("Node %u: Sending Reg-1\n", id_d);
                COAP_BLOCKING_REQUEST(&ep_as, request, client_reg1_handler);

                reg = 1;

                /* --- Enrollment energy snapshot (after) --- */
                print_energest_stats(&cpu_enroll_after, &energy_enroll_after);

            /* ============================================================
             * AUTH + DATA — same timer tick, measurement window matches
             * base scheme's auth==1 block (key-update + data).
             *
             * Base scheme auth==1:  [BEFORE] keyupdate COAP + data COAP [AFTER]
             * Our scheme equiv:     [BEFORE] auth COAP   + data COAP [AFTER]
             *
             * BEFORE snapshot taken at start of block — identical to base.
             * AFTER  snapshot taken after data confirmed — identical to base.
             * Reported: (cpu_auth - cpu_reg) and (energy_auth - energy_reg)
             * ============================================================ */
            } else if (count < 1) {

                /* === BEFORE snapshot — same position as base scheme === */
                print_energest_stats(&cpu_reg, &energy_reg);

                /* --- Auth COAP (our scheme: includes key exchange) --- */
                uint8_t R_d = h_d;

                uint8_t pid_buf[33];
                pid_buf[0] = id_d;
                memcpy(pid_buf + 1, m_d, 32);
                H(pid_buf, 33, auth_PID);

                H(&y_d, 1, auth_Y_dH);

                uint8_t mask_in[66], mask[32];
                mask_in[0] = R_d;
                memcpy(mask_in + 1,  m_d,      32);
                memcpy(mask_in + 33, auth_PID, 32);
                mask_in[65] = ts_1;
                H(mask_in, 66, mask);

                uint8_t y_asd[32];
                for (int i = 0; i < 32; i++) y_asd[i] = auth_Y_dH[i] ^ mask[i];

                uint8_t pa[65];
                memcpy(pa,      auth_PID, 32);
                memcpy(pa + 32, y_asd,   32);
                pa[64] = ts_1;

                coap_init_message(request, COAP_TYPE_CON, COAP_POST, 2);
                coap_set_header_uri_path(request, "test/auth");
                coap_set_payload(request, pa, 65);
                t_auth_start = clock_time();
                printf("Node %u: Sending auth. PID=%02x%02x%02x ts_1=%u\n",
                       id_d, auth_PID[0], auth_PID[1], auth_PID[2], ts_1);
                COAP_BLOCKING_REQUEST(&ep_as, request, client_auth_handler);
                /* After this returns: k_gw_d and PID are set by handler */

                /* --- Data COAP (same tick, same as base scheme) --- */
                uint8_t sensor[16];
                memset(sensor, 0, 16);
                sensor[0] = 9;

                uint8_t K_AES[16];
                memcpy(K_AES, k_gw_d, 16);
                aes_enc(K_AES, sensor, 1);

                uint8_t pd[48];
                memcpy(pd,      PID,    32);
                memcpy(pd + 32, sensor, 16);

                coap_init_message(request, COAP_TYPE_CON, COAP_POST, 3);
                coap_set_header_uri_path(request, "test/data");
                coap_set_payload(request, pd, 48);
                t_data_start = clock_time();
                printf("Node %u: Sending data\n", id_d);
                COAP_BLOCKING_REQUEST(&ep_gw, request, client_data_handler);

                count++;

                /* === AFTER snapshot + print — IDENTICAL to base scheme ===
                 * Base scheme: if(count==1) { print_energest_stats(&cpu_auth,&energy_auth);
                 *                             printf(...cpu_auth-cpu_reg...energy_auth-energy_reg); }
                 */
                if (count == 1) {
                    print_energest_stats(&cpu_auth, &energy_auth);
                    printf("\nNode %u: The CPU time and energy at the end of authentication"
                           " %u for client %u are %f and %f\n",
                           id_d, count, id_d,
                           (cpu_auth - cpu_reg),
                           (energy_auth - energy_reg));

                    /* =====================================================
                     * COMPREHENSIVE METRICS SUMMARY
                     * ===================================================== */
                    printf("\n============ PROTOCOL METRICS SUMMARY (Node %u) ============\n", id_d);

                    printf("--- Phase Timing ---\n");
                    printf("  Enrollment       : %lu ms\n", metric_enroll_ms);
                    printf("  Auth+KE RTT      : %lu ms\n", metric_auth_ms);
                    printf("  Data RTT         : %lu ms\n", metric_data_ms);

                    printf("--- Energy Consumption ---\n");
                    printf("  Enrollment CPU   : %f s\n",
                           cpu_enroll_after - cpu_enroll_before);
                    printf("  Enrollment Energy: %f J\n",
                           energy_enroll_after - energy_enroll_before);
                    printf("  Auth+Data CPU    : %f s\n",
                           cpu_auth - cpu_reg);
                    printf("  Auth+Data Energy : %f J\n",
                           energy_auth - energy_reg);

                    printf("--- Communication Overhead (bytes) ---\n");
                    printf("  Reg-0 req/resp   : 16 / 48\n");
                    printf("  Reg-1 req/resp   : 48 / 10\n");
                    printf("  Auth  req/resp   : 65 / 34\n");
                    printf("  Token (AS->GW)   : 81\n");
                    printf("  Data  req/resp   : 48 / 1\n");
                    printf("  Enrollment total : 122 bytes\n");
                    printf("  Auth+KE+Data tot : 229 bytes\n");

                    printf("--- Storage Overhead (Device) ---\n");
                    printf("  Shared key       : %u bytes\n",
                           (unsigned)sizeof(K_AS_D));
                    printf("  Session state    : %u bytes\n",
                           (unsigned)(sizeof(m_d) + sizeof(k_gw_d) +
                                     sizeof(PID) + sizeof(c_d) +
                                     sizeof(c_as_d) + sizeof(y_d) +
                                     sizeof(h_d) + sizeof(ts_1) +
                                     sizeof(last_ts2)));
                    printf("  Total device mem : %u bytes\n",
                           (unsigned)(sizeof(K_AS_D) + sizeof(id_d) +
                                     sizeof(id_as) + sizeof(c_d) +
                                     sizeof(c_as_d) + sizeof(y_d) +
                                     sizeof(h_d) + sizeof(ts_1) +
                                     sizeof(last_ts2) + sizeof(m_d) +
                                     sizeof(k_gw_d) + sizeof(PID) +
                                     sizeof(auth_PID) + sizeof(auth_Y_dH) +
                                     sizeof(reg) + sizeof(count)));

                    printf("=============================================================\n\n");
                }

            /* ============================================================
             * ONGOING DATA — keep sending with session key (count >= 1)
             * ============================================================ */
            } else {
                uint8_t sensor[16];
                memset(sensor, 0, 16);
                sensor[0] = 9;

                uint8_t K_AES[16];
                memcpy(K_AES, k_gw_d, 16);
                aes_enc(K_AES, sensor, 1);

                uint8_t pd[48];
                memcpy(pd,      PID,    32);
                memcpy(pd + 32, sensor, 16);

                coap_init_message(request, COAP_TYPE_CON, COAP_POST, 3);
                coap_set_header_uri_path(request, "test/data");
                coap_set_payload(request, pd, 48);
                t_data_start = clock_time();
                COAP_BLOCKING_REQUEST(&ep_gw, request, client_data_handler);
            }

            /* IDENTICAL to base scheme */
            etimer_reset(&et);
        }
    }

    PROCESS_END();
}
