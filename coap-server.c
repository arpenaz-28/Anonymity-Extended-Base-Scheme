/*
 * Copyright (c) 2013, Institute for Pervasive Computing, ETH Zurich
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file is part of the Contiki operating system.
 */

/**
 * \file
 *      Erbium (Er) CoAP Engine example.
 * \author
 *      Matthias Kovatsch <kovatsch@inf.ethz.ch>
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "contiki.h"
#include "coap-engine.h"
#include "aes.h"
#include "coap-blocking-api.h"
#include "random.h"

#include "sys/node-id.h"
#include "sys/energest.h"
#include "lib/sha256.h"
#include "net/ipv6/uip-ds6.h"
#include "net/netstack.h"
#include "net/routing/routing.h"
#include "net/routing/rpl-lite/rpl.h"
#include "net/ipv6/uip-debug.h"
//#include "coap-forwarding.h"
#include "net/ipv6/uiplib.h"
#include "net/mac/tsch/tsch.h"
#define LOG_MODULE "coap-bt-server"
#define LOG_LEVEL LOG_LEVEL_INFO
/* Voltage and current values for native platform (simulate like Z1) */
#define CURRENT_CPU     1.8e-3     // in Amps
#define CURRENT_LPM     0.0545e-3
#define CURRENT_TX      17.4e-3
#define CURRENT_RX      18.8e-3
#define SUPPLY_VOLTAGE  3.0     
 
 #define MAX_CLIENTS 10
#define TOKEN_LEN 48
//#define LOG_CONF_LEVEL_RPL LOG_LEVEL_NONE
#include "sys/log.h"


#define KEY_LENGTH 16

// Globals and variables from your existing code ...
static uint8_t  hpayload[34],payload[16],data_c[35],auth=0;
uint8_t k_as_d[16] = {0x67, 0x61, 0x74, 0x73, 0x20, 0x6D, 0x79, 0x20, 0x4B, 0x75, 0x6F, 0x67, 0x20, 0x46, 0x75};
uint8_t k_gw_as[16] = {0x67, 0x62, 0x74, 0x73, 0x20, 0x6D, 0x79, 0x20, 0x4B, 0x75, 0x6F, 0x67, 0x20, 0x46, 0x75};
 static coap_endpoint_t server_ep1;
 static coap_message_t request_a[1];
static uint8_t auth_tokens[MAX_CLIENTS][TOKEN_LEN];
static uint8_t token_count = 0;
static uint8_t sent_index = 0;

process_event_t event_trigger_gateway_send;
uint8_t T_Acc[32]={1},Y_d_H[32], c_d=6,k_gw_d[33], hash_dash[32], data[68], n[32],n_d=2;
uint8_t auth_id_ts[16],key1[16],key2[16],auth_token[48];
uint8_t ts_1 = 0, ts_2 = 1, ts_3 = 2,ts_4=3, auth_time,id_d_d;
int count = 0;
//static struct etimer et;

typedef struct client{
        uint8_t ID_d;
	uint8_t y_d;
	uint8_t M_d[32];
	uint8_t c_as_d;
	uint8_t PHI_d;
	uint8_t h_as_d;
	
	
}client;


client c[10];
double cpu_auth;
double energy_auth;
static void print_energest_stats(  double *seconds_cpu,double *total_energy) {
  energest_flush(); // Always flush before reading

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

 // printf("\n--- Energest Statistics ---\n");
  //printf("CPU Active Time   : %lu ticks (%.3f s)\n", cpu_ticks, seconds_cpu);
 // printf("LPM Time          : %lu ticks (%.3f s)\n", lpm_ticks, seconds_lpm);
 // printf("Transmit Time     : %lu ticks (%.3f s)\n", tx_ticks, seconds_tx);
  //printf("Listen Time       : %lu ticks (%.3f s)\n", rx_ticks, seconds_rx);
 // printf("Estimated Energy  : %.6f J\n", total_energy);
//  return (cpu_ticks,total_energy);
//  printf("---------------------------\n");
}
static bool discover_peer_to_authenticate_with(void) {
 // (void)uint16_t target_peer_id = 2;
  uip_ipaddr_t server1_ipaddr;

  uip_ip6addr_u8(&server1_ipaddr, 0xfd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                  0x02, 0x01, 0x00, 0x01, 0x00, 0x01, 0x00, 0x01);

  uip_ipaddr_copy(&server_ep1.ipaddr, &server1_ipaddr);
  server_ep1.port = UIP_HTONS(COAP_DEFAULT_PORT);
  server_ep1.secure = 0;

 // LOG_INFO("Node %u: Selected peer Node %u for mutual auth at ", node_id, target_peer_id);
 // LOG_INFO_6ADDR(&server_ep1.ipaddr);
 // LOG_INFO_("\n");
  return true;
}

PROCESS(coap_server, "CoAP Server");
PROCESS_THREAD(coap_server, ev, data);
uint8_t simulate_puf_response(uint8_t c)
{
    uint8_t response;
    uint8_t path1 = random_rand() ^ c;
    uint8_t path2 = random_rand() ^ c;
    (path1 > path2) ? (response = 1) : (response = 0);
    LOG_DBG("Simulate PUF response: challenge=%u response=%u\n", c, response);
    return response;
}

void generate_helper(uint8_t response, uint8_t *helper, uint8_t *secret)
{
    *secret = 1;
    *helper = *secret & response;
}

uint8_t regenerate_response(uint8_t challenge, uint8_t helper)
{
    uint8_t response;
    (helper == 0) ? (response = helper & challenge) : (response = helper || challenge);
    return response;
}




void server_authtoken_handler(coap_message_t *response) {
  const uint8_t *chunk;
  if (!response || coap_get_payload(response, &chunk) == 0) {
    printf("No authoken response payload");
    return;
  }
  printf("%s",chunk);
  memset(auth_tokens+sent_index,0,16);
  sent_index=(sent_index + 1) % 10;
  
}



static void res_reg_handler(coap_message_t *request, coap_message_t *response,
                            uint8_t *buffer, uint16_t preferred_size, int32_t *offset) {
                            
    LOG_INFO("Handler reg called!\n"); 
  //  print_energest_stats(&cpu_start,&energy_start);
  const uint8_t *chunk;
  int len = coap_get_payload(request, &chunk);
  if(len==16)
  {
        memset(payload,0,16);
        memcpy(payload,chunk,16);
        struct AES_ctx aes_ctx_ch_d;
        AES_init_ctx(&aes_ctx_ch_d,k_as_d);
        AES_ECB_decrypt(&aes_ctx_ch_d,payload);
  	uint8_t id_d=payload[0];
  	if((c[id_d % 10].ID_d==id_d) || (count>10) )
  	{
  	        
  		printf("\n already registered or server unavailable");
  		return;
  	}
  	count++;
  	c[id_d % 10].ID_d=id_d;
  	
  	memset(payload,0,16);
  	c[id_d %10].M_d[0]=5;
  	payload[0]=c_d;
  	payload[1]=c[id_d % 10].M_d[0];
  	AES_init_ctx(&aes_ctx_ch_d,k_as_d);
        AES_ECB_encrypt(&aes_ctx_ch_d,payload);
        coap_set_payload(response,payload,sizeof(payload));

        
  	
  }
  else{
  	printf("\n No request");
  }


}



static void res_reg1_handler(coap_message_t *request, coap_message_t *response,
                             uint8_t *buffer, uint16_t preferred_size, int32_t *offset) {
                             
  LOG_INFO("Handler reg1 called!\n"); 
  char *message="Registered";
  const uint8_t *chunk;
  int len = coap_get_payload(request, &chunk);

  if (len != 16) {
    LOG_WARN("Invalid reg1 payload\n");
    return;
  }

  memset(payload,0,16);
  memcpy(payload,chunk,16);
  struct AES_ctx aes_ctx_ch_d;
  AES_init_ctx(&aes_ctx_ch_d,k_as_d);
  AES_ECB_decrypt(&aes_ctx_ch_d,payload);
  
  uint8_t id_d=payload[0];
  c[id_d % 10].y_d=payload[1];

  uint8_t R_d= payload[2];
 printf("\n during reg R_d is %u",R_d);
  c[id_d % 10].c_as_d=payload[3];
  uint8_t R_as_d=simulate_puf_response(c[id_d % 10].c_as_d);
  uint8_t secret;
  generate_helper(R_as_d, &c[id_d % 10].h_as_d , &secret);
  c[id_d % 10].PHI_d=R_d ^ R_as_d;
  c[id_d % 10].M_d[0]=5;

  memset(Y_d_H,0,32);
  SHA256_CTX sha_ctx;
  sha256_init(&sha_ctx);
  sha256_update(&sha_ctx, &c[id_d % 10].y_d, 1);
  sha256_final(&sha_ctx, Y_d_H);
  for(int i=0;i<32;i++)
  {
  	T_Acc[i]=1;
  }
  for(int i=0;i<32;i++)
  {
  	T_Acc[i]=T_Acc[i] & Y_d_H[i];
  }
  
   /*printf("\n Hashed value of y_d");
      for(int i=0;i<32;i++)
      {
      	printf("%u",Y_d_H[i]);
      }*/
  
  coap_set_payload(response,(uint8_t *)message,strlen(message));
 
 //   cpu_reg=cpu_end-cpu_start;
  //  printf("\n%f",cpu_reg);
 

       
}

// Protothread to perform blocking request

//print_energest_stats(&cpu_reg,&energy_reg);

static void res_auth_handler(coap_message_t *request, coap_message_t *response,
    
                            uint8_t *buffer, uint16_t preferred_size, int32_t *offset) {
                            
                            
                            
                            
 //  print_energest_stats(&cpu_reg,&energy_reg);                        
  LOG_INFO("Handler auth called!\n"); 
   
  const uint8_t *chunk;
  int len = coap_get_payload(request, &chunk);

  if (len == 0) {
    LOG_WARN("Empty auth1 payload\n");
    return;
  }
  memset(hpayload,0,34);
  memcpy(hpayload,chunk,34);
  uint8_t id_d=hpayload[0];
  uint8_t ts_1=hpayload[33];
  if(c[id_d % 10].ID_d != id_d)
  {
  	printf("\n Not registered");
  	return;
  }
  
  memset(Y_d_H,0,32);
  memcpy(Y_d_H,hpayload+1,32);
  
  memset(data_c,0,35);
  uint8_t R_as_d=regenerate_response(c[id_d % 10].c_as_d, c[id_d % 10].h_as_d);
  uint8_t R_d= c[id_d % 10].PHI_d ^ R_as_d;
  data_c[0]=R_d;
  printf("\n the value of R_d is %u", R_d);
  printf("\n the value of M_d is %u", c[id_d % 10].M_d[0]);
  memcpy(data_c+1,c[id_d % 10].M_d,32);
  
  data_c[33]=id_d;
  data_c[34]=ts_1;
 
  SHA256_CTX sha_ctx;
  sha256_init(&sha_ctx);
  sha256_update(&sha_ctx, data_c, 35);
   sha256_final(&sha_ctx, hash_dash);
  
  for(int i=0;i<32;i++)
  	Y_d_H[i]=Y_d_H[i] ^ hash_dash[i];
  
 /*  printf("\n Hashed value of y_d");
      for(int i=0;i<32;i++)
      {
      	printf("%u",Y_d_H[i]);
      }*/
  
  for(int i=0;i<32;i++)
  {
  	if(T_Acc[i]!=(T_Acc[i] & Y_d_H[i]))
  	{
  		printf("\n Not present");
  		return;
  		}
  }
  auth_time = (uint8_t)(clock_time() / CLOCK_SECOND);
  uint8_t ts_2=1;

  
  
  memset(data,0,68);
  memcpy(data, Y_d_H,32);
  memcpy(data+32,c[id_d % 10].M_d,32);
   printf("\n the value of M_d is %u",c[id_d % 10].M_d[0]);
  data[64]=R_d;
   printf("\n the value of R_d is %u",R_d);
  data[65]=node_id;
  data[66]=id_d;
   printf("\n the value of id_d is %u",id_d);
  data[67]=ts_2;
  
  memset(hash_dash,0,32);
  sha256_init(&sha_ctx);
  sha256_update(&sha_ctx, data, 68);
  sha256_final(&sha_ctx, hash_dash);
  /*  printf("\n The value of session key is mask");
  for(int i=0;i<32;i++)
  {
  	printf("%u\n",hash_dash[i]);
  }*/
  memset(n,0,32);
  sha256_init(&sha_ctx);
  sha256_update(&sha_ctx, &n_d, 1);
  sha256_final(&sha_ctx, n);
  
 /* printf("\n The value of session key is n");
  for(int i=0;i<32;i++)
  {
  	printf("%u\n",n[i]);
  }*/
  for(int i=0;i<32;i++)
  	hash_dash[i]=hash_dash[i] ^ n[i];
  memset(hpayload,0,34);
  hpayload[0]=node_id;
  memcpy(hpayload+1,hash_dash,32);
  hpayload[33]=ts_2;
 /* printf("\n The value of payload is n");
  for(int i=0;i<34;i++)
  {
  	printf("%u\n",hpayload[i]);
  }*/

  coap_set_payload(response,hpayload,sizeof(hpayload));
  
 print_energest_stats(&cpu_auth,&energy_auth);
 printf("\n The CPU time and energy at the end of authentication for server %u are %f and %f",node_id,(cpu_auth),(energy_auth));
 
 printf("\n Hpayload sent"); 
 auth=1;
 memset(auth_id_ts,0,16);
 auth_id_ts[0]=id_d;
 auth_id_ts[1]=node_id;
 auth_id_ts[2]=auth_time;
 struct AES_ctx aes_ctx_ch_d;
 AES_init_ctx(&aes_ctx_ch_d,k_gw_as);
 AES_ECB_encrypt(&aes_ctx_ch_d,auth_id_ts);
 
 for(int i=0;i<32;i++)
 {
 	c[id_d % 10].M_d[i]=n[i];
 }
 memset(k_gw_d,0,33);
 k_gw_d[0]=R_d;
 memcpy(k_gw_d +1 ,c[id_d % 10].M_d,32);
 sha256_init(&sha_ctx);
 sha256_update(&sha_ctx, k_gw_d, 33);
 sha256_final(&sha_ctx, hash_dash);
 
 memset(key1,0,16);
 memset(key2,0,16);
 memcpy(key1,hash_dash,16);
 memcpy(key2,hash_dash +16,16);
 /* printf("\n The value of session key is k_gw_d");
  for(int i=0;i<32;i++)
  {
  	printf("%u",hash_dash[i]);
  }*/
    
 AES_init_ctx(&aes_ctx_ch_d,k_gw_as);
 AES_ECB_encrypt(&aes_ctx_ch_d,key1);
 
 AES_init_ctx(&aes_ctx_ch_d,k_gw_as);
 AES_ECB_encrypt(&aes_ctx_ch_d,key2);
 
 memset(auth_token,0,48);
 memcpy(auth_token,auth_id_ts,16);
 memcpy(auth_token+16,key1,16);
 memcpy(auth_token+32,key2,16);
  printf("\n The token count and send index is %u and %u before if ",token_count,sent_index);
    if( token_count < MAX_CLIENTS) {
      if(token_count==sent_index)
    {
    	sent_index=0;
    	token_count=0;
    }
    
    memset(auth_tokens[token_count], 0, TOKEN_LEN);
    memcpy(auth_tokens[token_count], auth_token, 48);
    token_count=(token_count + 1) % 10;
     printf("\n The token count and send index is %u and %u in the if",token_count,sent_index);
    process_post(&coap_server, event_trigger_gateway_send, NULL);
   
    
    
  }
  
 
 printf("\n The token count and send index is %u and %u",token_count,sent_index);

 
}





//extern coap_resource_t res_reg;
//extern coap_resource_t res_reg1;
//extern coap_resource_t res_auth1;
//extern coap_resource_t res_auth2;

RESOURCE(res_reg,"title=\"Hello reg: ?len=0..\";rt=\"Text\"",res_reg_handler,NULL,NULL,NULL);
RESOURCE(res_reg1,"title=\"Hello reg1: ?len=0..\";rt=\"Text\"",res_reg1_handler,NULL,NULL,NULL);
RESOURCE(res_auth,"title=\"Hello auth: ?len=0..\";rt=\"Text\"",NULL,res_auth_handler,NULL,NULL);


/*---------------------------------------------------------------------------*/

AUTOSTART_PROCESSES(&coap_server);


/*---------------------------------------------------------------------------*/
PROCESS_THREAD(coap_server, ev, data)
{
  
  PROCESS_BEGIN();

  //static coap_endpoint_t endpoint;

  /* Initialize the CoAP engine */
   // NETSTACK_MAC.on();
 // tsch_set_coordinator(1);
  coap_engine_init();

  /* Reduce RPL logging verbosity */
  rpl_dag_t *dag = rpl_get_any_dag();
  if(dag != NULL) {
    char ipstr[UIPLIB_IPV6_MAX_STR_LEN];
    uiplib_ipaddr_snprint(ipstr, sizeof(ipstr), &dag->prefix_info.prefix);
    LOG_DBG("Node is joined to DAG with prefix %s\n", ipstr);
  } else {
    LOG_DBG("Node is not joined to any DAG yet\n");
  }

  /* Print global IPv6 address - Debug only */
  for(int i = 0; i < UIP_DS6_ADDR_NB; i++) {
    if(uip_ds6_if.addr_list[i].isused &&
       uip_ds6_if.addr_list[i].state == ADDR_PREFERRED) {
       
      LOG_DBG("Node global IPv6 address: ");
      LOG_DBG_6ADDR(&uip_ds6_if.addr_list[i].ipaddr);
      LOG_DBG_("\n");
      break;
    }
  }
  /* Activate the resources */
  
  discover_peer_to_authenticate_with();
  
 
  coap_activate_resource(&res_reg, "test/reg");
  coap_activate_resource(&res_reg1, "test/reg1");
  coap_activate_resource(&res_auth, "test/auth");
  
 // NETSTACK_MAC.off(1);

  LOG_INFO("Starting CoAP server\n");

  event_trigger_gateway_send = process_alloc_event();
   static uint8_t payloads[48];

  while(1) {
   // PROCESS_YIELD();
     PROCESS_WAIT_EVENT_UNTIL(ev == event_trigger_gateway_send);
printf("\n The token count and send index is %u and %u before while",token_count,sent_index);
    if(sent_index <token_count) {
      memset(payloads, 0, sizeof(payloads));
      memcpy(payloads, auth_tokens[sent_index],48);

     

      coap_init_message(request_a, COAP_TYPE_CON, COAP_GET, coap_get_mid());
      coap_set_header_uri_path(request_a, "test/auth_token");
      coap_set_payload(request_a, payloads, sizeof(payloads));
      LOG_INFO("Token count = %d, Sent index = %d\n", token_count, sent_index);
      COAP_BLOCKING_REQUEST(&server_ep1, request_a, server_authtoken_handler);
     // token_count--;

      // Trigger next token send if available
      if(sent_index <token_count) {
        process_post(&coap_server, event_trigger_gateway_send, NULL);
      }
    }
  
 
    
}
  PROCESS_END();
}



