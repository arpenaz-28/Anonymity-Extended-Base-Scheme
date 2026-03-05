#include <stdio.h>
#include "net/ipv6/uip-ds6.h"
#include <stdlib.h>
#include <string.h>
#include "contiki.h"
#include "contiki-net.h"
#include "coap-engine.h"
#include "aes.h"

#include "lib/sha256.h"
#include "coap-blocking-api.h"
#include "net/mac/tsch/tsch.h"
#include "sys/node-id.h"

#include "net/ipv6/uip-debug.h"
#include "net/ipv6/uiplib.h"
#include "sys/energest.h"
#define CURRENT_CPU     1.8e-3     // in Amps
#define CURRENT_LPM     0.0545e-3
#define CURRENT_TX      17.4e-3
#define CURRENT_RX      18.8e-3
#define SUPPLY_VOLTAGE  3.0  
//#define LOG_MODULE "Client-Node"
//#define LOG_LEVEL LOG_LEVEL_INFO   // Show INFO and above, hide DEBUG logs
//#include "sys/log.h"

#define KEY_LENGTH 16


//static uint8_t e, d, n;
static uint8_t id_d, id_as=2, h_d,  y_d = 2, c_as_d=3, c_d, m_d, ts_1 = 0, ts_2 = 1,h_d;
uint8_t k_as_d[16] = {0x67, 0x61, 0x74, 0x73, 0x20, 0x6D, 0x79, 0x20, 0x4B, 0x75, 0x6F, 0x67, 0x20, 0x46, 0x75};
static uint8_t g=5,p=23,a=5;
uint8_t reg = 0, auth = 0,M_d[32],k_gw_d[32],K_GW_D[16];

static uint8_t payload[16],hash[32],hpayload[34];
static coap_endpoint_t server_ep1, server_ep2;
uint8_t count=0;
double cpu_reg,cpu_auth,cpu_start;
  double energy_reg,energy_auth,energy_start;
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

uint8_t simulate_puf_response(uint8_t c)
{
    uint8_t response;
    uint8_t path1 = random_rand() ^ c;
    uint8_t path2 = random_rand() ^ c;
    (path1 > path2) ? (response = 1) : (response = 0);
    printf("Simulate PUF response: challenge=%u response=%u\n", c, response);
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


static bool discover_peer_to_authenticate_with(void) {
 // (void)uint16_t target_peer_id = 2;
  uip_ipaddr_t server1_ipaddr;

  uip_ip6addr_u8(&server1_ipaddr, 0xfd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                  0x02, 0x02, 0x00, 0x02, 0x00, 0x02, 0x00, 0x02);

  uip_ipaddr_copy(&server_ep1.ipaddr, &server1_ipaddr);
  server_ep1.port = UIP_HTONS(COAP_DEFAULT_PORT);
  server_ep1.secure = 0;

 // LOG_INFO("Node %u: Selected peer Node %u for mutual auth at ", node_id, target_peer_id);
 // LOG_INFO_6ADDR(&server_ep1.ipaddr);
 // LOG_INFO_("\n");
  return true;
}

static bool discover_peer_to_authenticate_with1(void) {
 // (void)uint16_t target_peer_id = 1;
  uip_ipaddr_t server2_ipaddr;

  uip_ip6addr_u8(&server2_ipaddr, 0xfd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                  0x02, 0x01, 0x00, 0x01, 0x00, 0x01, 0x00, 0x01);

  uip_ipaddr_copy(&server_ep2.ipaddr, &server2_ipaddr);
  server_ep2.port = UIP_HTONS(COAP_DEFAULT_PORT);
  server_ep2.secure = 0;

 // LOG_INFO("Node %u: Selected peer Node %u for mutual auth at ", node_id, target_peer_id);
 // LOG_INFO_6ADDR(&server_ep2.ipaddr);
 // LOG_INFO_("\n");
  return true;
}




void client_reg_handler(coap_message_t *response) {
  const uint8_t *chunk;
  if (!response || coap_get_payload(response, &chunk) == 0) {
   // LOG_WARN("No reg payload");
    return;
  }
  memset(payload,0,16);
  memcpy(payload, chunk, 16);
  
 /* for(int i=0;i<16;i++)
  {
  	printf("\n%u",payload[i]);
  }*/
  printf("Received reg payload\n");
}



void client_reg1_handler(coap_message_t *response) {
  const uint8_t *chunk;
  if (coap_get_payload(response, &chunk)) {
    reg = 1;
    printf("%s",chunk);
   }
}

void client_auth_handler(coap_message_t *response) {
  const uint8_t *chunk;
  if (!response || coap_get_payload(response, &chunk) == 0) {
    printf("No auth payload");
    return;
  }
  memset(hpayload,0,34);
  memcpy(hpayload,chunk,34);
  /*  printf("\n The value of payload is n");
  for(int i=0;i<33;i++)
  {
  	printf("%u\n",hpayload[i]);
  }*/

}


void client_key_update_handler(coap_message_t *response)
{
	const uint8_t *chunk;
	if(coap_get_payload(response,&chunk))
	{
	        
	      memset(payload,0,16);
	      memcpy(payload,chunk,16);
	      struct AES_ctx aes_ctx_ch_d;
	      AES_init_ctx(&aes_ctx_ch_d,K_GW_D);
	      AES_ECB_decrypt(&aes_ctx_ch_d,payload);
	      
	      uint8_t beta=payload[0];
	      printf("\n the value of beta in client side is %u",beta);
	      k_gw_d[0]=(beta^a)% p;
	       
	      printf("\n The value of k_gw_d is %u",k_gw_d[0]);
	       
	        
	        
	}
	else
	{
		printf("\n No payload");
	
	}
	
}



void client_data_handler(coap_message_t *response) {
  const uint8_t *chunk;
  int len = coap_get_payload(response, &chunk);
  printf("Data length: %u\n", len);
  if (!response || len == 0) {
    printf("No data payload");
  } else {
    auth=chunk[0];
    printf("Data payload: %u\n", auth);
  }
}



PROCESS(er_example_client, "Erbium Example Client");
AUTOSTART_PROCESSES(&er_example_client);

static struct etimer et;
static coap_message_t request[1];

PROCESS_THREAD(er_example_client, ev, data)
{
  PROCESS_BEGIN();
 // NETSTACK_MAC.on();
 // tsch_set_coordinator(0);
  NETSTACK_ROUTING.init();
  rpl_dag_t *dag = rpl_get_any_dag();
  if (dag != NULL) {
    char ipstr[UIPLIB_IPV6_MAX_STR_LEN];
    uiplib_ipaddr_snprint(ipstr, sizeof(ipstr), &dag->prefix_info.prefix);
    //LOG_DBG("Node is joined to DAG with prefix %s\n", ipstr);  // RPL logs as DEBUG now
  } else {
   // LOG_WARN("Node is not joined to any DAG yet\n");
  }

  for (int i = 0; i < UIP_DS6_ADDR_NB; i++) {
    if (uip_ds6_if.addr_list[i].isused && uip_ds6_if.addr_list[i].state == ADDR_PREFERRED) {
   //   LOG_DBG("Node global IPv6 address: ");
   //   LOG_DBG_6ADDR(&uip_ds6_if.addr_list[i].ipaddr);
    //  LOG_DBG_("\n");
      break;
    }
  }

  discover_peer_to_authenticate_with();
  discover_peer_to_authenticate_with1();

  etimer_set(&et, CLOCK_SECOND * (5+node_id));

  while (1) {
    PROCESS_YIELD();
    
    if (etimer_expired(&et)) {
     
      if (reg == 0) {
       
       // energest_flush();          
       //energest_flush();
     //  uint64_t cpu_start = energest_type_time(ENERGEST_TYPE_CPU);
    //   uint64_t tx_start = energest_type_time(ENERGEST_TYPE_TRANSMIT);
  //     uint64_t rx_start  = energest_type_time(ENERGEST_TYPE_LISTEN);           
      // energest_on(ENERGEST_TYPE_CPU);
     //  energest_on(ENERGEST_TYPE_TRANSMIT);
      // energest_on(ENERGEST_TYPE_LISTEN);
      // print_energest_stats(&cpu_start,&energy_start);
      id_d = node_id;
      /*  generateKeys(&e, &d, &n);
        printf("RSA Keys - e: %u, d: %u, n: %u\n", e, d, n);*/
        
      memset(payload,0,16);
      payload[0]=id_d;
      struct AES_ctx aes_ctx_ch_d;
      AES_init_ctx(&aes_ctx_ch_d,k_as_d);
      AES_ECB_encrypt(&aes_ctx_ch_d,payload);
  
     // coap_endpoint_parse(SERVER_EP, strlen(SERVER_EP), &server_ep);
      coap_init_message(request, COAP_TYPE_CON, COAP_GET, 0);
      coap_set_header_uri_path(request, "test/reg");
      coap_set_payload(request, payload, 16);

      printf("Sending registration request to server...\n");
      COAP_BLOCKING_REQUEST(&server_ep1, request, client_reg_handler);

      AES_init_ctx(&aes_ctx_ch_d,k_as_d);
      AES_ECB_decrypt(&aes_ctx_ch_d,payload);
      c_d=payload[0];
      m_d=payload[1];
       memset(M_d,0,32);
      memcpy(M_d,&m_d,1);
      memset(payload,0,16);
      payload[0]=id_d;
      payload[1]=y_d;
     
      uint8_t R_d=simulate_puf_response(c_d);
      uint8_t secret;
      generate_helper(R_d, &h_d, &secret);
      payload[2]=R_d;
      payload[3]=c_as_d;
      AES_init_ctx(&aes_ctx_ch_d,k_as_d);
      AES_ECB_encrypt(&aes_ctx_ch_d,payload);
      coap_init_message(request, COAP_TYPE_CON, COAP_GET, 1);
      coap_set_header_uri_path(request, "test/reg1");
      coap_set_payload(request, payload, sizeof(payload));
     // for (int i = 0; i < 16; i++) printf("\n %u",payload[i]);
      printf("Sending reg1 request\n");
      reg=1;
      COAP_BLOCKING_REQUEST(&server_ep1, request, client_reg1_handler);
      
  
     }
       
        
     else if (auth == 0 && count<20) {
     
     	
     
     // printf("\n The CPU time and energy at the end of registration for client %u are %f and %f",id_d,cpu_reg,energy_reg);
      uint8_t R_d=regenerate_response(c_d, h_d);
      static uint8_t Y_d_H[32];
      memset(Y_d_H,0,32);
      SHA256_CTX sha_ctx;
      sha256_init(&sha_ctx);
      sha256_update(&sha_ctx, &y_d, 1);
      sha256_final(&sha_ctx, Y_d_H);
      
     /* printf("\n Hashed value of y_d");
      for(int i=0;i<32;i++)
      {
      	printf("%u",Y_d_H[i]);
      }*/
     
      
      uint8_t data[35];
      memset(data,0,35);
      data[0]=R_d;
        printf("\n the value of R_d is %u",R_d);
      memcpy(data+1,M_d,32);
      printf("\n the value of M_d is %u",M_d[0]);
      data[33]=id_d;
      data[34]=ts_1;
      
      sha256_init(&sha_ctx);
      sha256_update(&sha_ctx, data, 35);
      sha256_final(&sha_ctx, hash);
      
      for(int i=0;i<32;i++)
      {
      	hash[i]=hash[i] ^ Y_d_H[i];
      }
      
      hpayload[0]=id_d;
     
     memcpy(hpayload+1,hash,32);
      hpayload[33]=ts_1;
      coap_init_message(request, COAP_TYPE_CON, COAP_POST, 2);
      coap_set_header_uri_path(request, "test/auth");
      coap_set_payload(request, hpayload, sizeof(hpayload));
      printf("\n Sending auth_request");
       
      COAP_BLOCKING_REQUEST(&server_ep1, request, client_auth_handler);
       
       
        
        
  
     
      R_d=regenerate_response(c_d, h_d);
      
      ts_2=hpayload[33];
       sha256_init(&sha_ctx);
      sha256_update(&sha_ctx, &y_d, 1);
      sha256_final(&sha_ctx, Y_d_H);
      printf("\n The timestamp is %u",ts_2);
      uint8_t data_dash[68];
      memset(data_dash,0,68);
      memcpy(data_dash,Y_d_H,32);
      memcpy(data_dash+32,M_d,32);
      printf("\n the value of M_d is %u",M_d[0]);
      memcpy(data_dash+64,&R_d,1);
       printf("\n the value of R_d is %u",R_d);
      memcpy(data_dash+65,&id_as,1);
        printf("\n the value of id_as is %u",id_as);
      memcpy(data_dash+66,&id_d,1);
        printf("\n the value of id_d is %u",id_d);
      memcpy(data_dash+67,&ts_2,1);
          printf("\n the value of ts_2 is %u",ts_2);
      sha256_init(&sha_ctx);
      sha256_update(&sha_ctx, data_dash, 68);
      sha256_final(&sha_ctx, hash);
      
     /* printf("\n The value of session key is mask 2");
  for(int i=0;i<32;i++)
  {
  	printf("%u",hash[i]);
  }*/
      memset(M_d,0,32);
      memcpy(M_d,hpayload+1,32);
      
      for(int i=0;i<32;i++)
      {
      	M_d[i]=M_d[i] ^ hash[i];
      } 
     /*  printf("\n The value of session key is n");
  for(int i=0;i<32;i++)
  {
  	printf("%u\n",M_d[i]);
  }
     
           printf("\n The value of mask");
  for(int i=0;i<32;i++)
  {
  	printf("%u\n",hash[i]);
  }*/
      uint8_t key[33];
      memset(key,0,33);
      key[0]=R_d;
      printf("\n The value of R_d is %u",R_d);
      memcpy(key+1,M_d,32);
      sha256_init(&sha_ctx);
      sha256_update(&sha_ctx, key, 33);
      sha256_final(&sha_ctx, k_gw_d);
       
      auth=1;
    
     
      }
     
      
 
      else if(auth==1)
      {
       
        /*  printf("\n The value of session key is k_gw_d");
          for(int i=0;i<32;i++)
          {
  	     printf("%u",k_gw_d[i]);
           }
     
        uint8_t data=9;
        printf("Authentication success, sending data request\n");
        coap_init_message(request, COAP_TYPE_CON, COAP_GET, 3);
        coap_set_header_uri_path(request, "test/data");
        uint8_t buffer[17];
        memset(buffer,0,17);
        buffer[0]=id_d;
        memset(payload,0,16);
        memcpy(payload,&data,sizeof(data));
        
        uint8_t K_GW_D[16];
        memset(K_GW_D,0,16);
        for(int i=0;i<16;i++)
        {
        	K_GW_D[i]=k_gw_d[i];
        	//printf("%u",K_GW_D[i]);
        }
          struct AES_ctx aes_ctx_ch_d;
      AES_init_ctx(&aes_ctx_ch_d,K_GW_D);
      AES_ECB_encrypt(&aes_ctx_ch_d,payload);
      memcpy(buffer+1,payload,sizeof(payload));
        coap_set_payload(request, buffer, sizeof(buffer));
        COAP_BLOCKING_REQUEST(&server_ep2, request, client_data_handler);*/
        
                print_energest_stats(&cpu_reg,&energy_reg);
         
	        coap_init_message(request, COAP_TYPE_CON, COAP_GET, 2);
	        coap_set_header_uri_path(request, "test/keyupdate");
	        uint8_t p1[17];
	        memset(p1,0,17);
	        memcpy(p1,&node_id,1);
	        memset(payload,0,16);
	       // memcpy(payload,&node_id,1);
	        uint8_t alpha= (g^ a) % p;
	        printf("\n the value of alpha in client side is %u",alpha);
	        memcpy(payload,&alpha,1);
	        // uint8_t K_GW_D[16];
                memset(K_GW_D,0,16);
                for(int i=0;i<16;i++)
                {
        	         K_GW_D[i]=k_gw_d[i];
        	//printf("%u",K_GW_D[i]);
                }
                struct AES_ctx aes_ctx_ch_d;
	        AES_init_ctx(&aes_ctx_ch_d,K_GW_D);
	        AES_ECB_encrypt(&aes_ctx_ch_d,payload);
	        memcpy(p1+1,payload,16);
	        printf("Sending request to gateway server endpoint\n");
	        coap_set_payload(request,p1,sizeof(p1));
	        COAP_BLOCKING_REQUEST(&server_ep2, request, client_key_update_handler);
	        
	       
	        
	        
	        printf("Authentication success, sending key update request\n");
	        printf("\n K_GW_D is being updated"); 
                for(int i=1;i<32;i++)
                {
                	k_gw_d[i]=0;
                }
	         
	         
	         
	         
	         uint8_t data=9;
                 printf("Key Update success, sending data request\n");
                 coap_init_message(request, COAP_TYPE_CON, COAP_GET, 3);
                 coap_set_header_uri_path(request, "test/data");
                 uint8_t buffer[17];
                 memset(buffer,0,17);
                 buffer[0]=id_d;
                 memset(payload,0,16);
                 memcpy(payload,&data,sizeof(data));
                 
                memset(K_GW_D,0,16);
                for(int i=0;i<16;i++)
                {
        	         K_GW_D[i]=k_gw_d[i];
        	//printf("%u",K_GW_D[i]);
                }
       
             //  struct AES_ctx aes_ctx_ch_d;
               AES_init_ctx(&aes_ctx_ch_d,K_GW_D);
               AES_ECB_encrypt(&aes_ctx_ch_d,payload);
               memcpy(buffer+1,payload,sizeof(payload));
               coap_set_payload(request, buffer, sizeof(buffer));
               COAP_BLOCKING_REQUEST(&server_ep2, request, client_data_handler);
               auth=0;
                count++;
      
         if(count==1)
         {
           print_energest_stats(&cpu_auth,&energy_auth);
           printf("\n The CPU time and energy at the end of authentication %u for client %u are %f and %f",count,id_d,(cpu_auth-cpu_reg),(energy_auth-energy_reg));
          }
        
        
    }
        
      /*  energest_off(ENERGEST_TYPE_CPU);
        energest_off(ENERGEST_TYPE_TRANSMIT);
        energest_off(ENERGEST_TYPE_LISTEN);
        energest_flush();
        uint64_t cpu_ticks = energest_type_time(ENERGEST_TYPE_CPU);
        uint64_t tx_ticks  = energest_type_time(ENERGEST_TYPE_TRANSMIT);
        uint64_t rx_ticks  = energest_type_time(ENERGEST_TYPE_LISTEN);
        //energest_flush();
        printf("\n ****) Total energy after authentication and data transfer is completed");
        printf("\nCPU active: %lu ticks\n", cpu_ticks);
        printf("\nRadio TX: %lu ticks\n", tx_ticks);
        printf("\nRadio RX: %lu ticks\n", rx_ticks);
 
        double cpu_j = (cpu_ticks * CPU_CURRENT_MA * VOLTAGE) / 1e9;
        double tx_j = (tx_ticks * TX_CURRENT_MA * VOLTAGE) / 1e9;
        double rx_j = (rx_ticks * RX_CURRENT_MA * VOLTAGE) / 1e9;
        double total_energy = cpu_j +tx_j+rx_j;
  
        printf("%fJ\n",total_energy);
        double processing_seconds = cpu_ticks / (double)ENERGEST_SECOND;
       printf("Processing Time after authenti is completed:%f sec",processing_seconds);*/
      

      etimer_reset(&et);
    }
  }

  PROCESS_END();
}

