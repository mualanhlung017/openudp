#include <signal.h>
#include <getopt.h>

#include <rte_eal.h>
#include <rte_common.h>
#include <rte_errno.h>
#include <rte_ethdev.h>
#include <rte_lcore.h>
#include <rte_mbuf.h>
#include <rte_mempool.h>
#include <rte_ring.h>
#include <rte_reorder.h>
#include <stdint.h>
#include <sys/queue.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#include <errno.h>
#include <signal.h>
#include <stdarg.h>
#include <inttypes.h>
#include <getopt.h>
#include <termios.h>
#include <unistd.h>
#include <pthread.h>

#include <rte_common.h>
#include <rte_log.h>
#include <rte_memory.h>
#include <rte_memcpy.h>
#include <rte_memzone.h>
#include <rte_eal.h>
#include <rte_per_lcore.h>
#include <rte_launch.h>
#include <rte_atomic.h>
#include <rte_cycles.h>
#include <rte_prefetch.h>
#include <rte_lcore.h>
#include <rte_per_lcore.h>
#include <rte_branch_prediction.h>
#include <rte_interrupts.h>
#include <rte_pci.h>
#include <rte_random.h>
#include <rte_debug.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_ring.h>
#include <rte_log.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>
#include <rte_memcpy.h>
#include <rte_ip.h>
#include <rte_tcp.h>
#include <rte_udp.h>
#include <rte_arp.h>
#include <rte_spinlock.h>
#include <rte_hash.h>
#include <rte_icmp.h>

#ifdef RTE_MACHINE_CPUFLAG_SSE4_2
#include <rte_hash_crc.h>
#define DEFAULT_HASH_FUNC       rte_hash_crc
#else
#include <rte_jhash.h>
#define DEFAULT_HASH_FUNC       rte_jhash
#endif

#define CTRL_MSG_INVALID 0xFFFFFFFF

#define IPv4_VERSION    4
#define IPv6_VERSION	6

#define MAX_BUF 2048
#define RX_DESC_PER_QUEUE 128
#define TX_DESC_PER_QUEUE 512

#define MAX_PKTS_BURST 32
#define REORDER_BUFFER_SIZE 8192
#define MBUF_PER_POOL 65535
#define MBUF_POOL_CACHE_SIZE 250

#define IP_TO_MAC_TABLE_SIZE 65536
#define TIMER_1SEC_DRAIN_US 1000000ULL
#define TIMER_1MILISEC_DRAIN_US 1000ULL
#define RING_SIZE 16384
#define MAX_SESSION 65536

/* uncommnet below line to enable debug logs */
/* #define DEBUG */

#ifdef DEBUG
#define LOG_LEVEL RTE_LOG_DEBUG
#define LOG_DEBUG(log_type, fmt, args...) RTE_LOG(DEBUG, log_type, fmt, ##args)
#else
#define LOG_LEVEL RTE_LOG_INFO
#define LOG_DEBUG(log_type, fmt, args...) do {} while (0)
#endif

/* Macros for printing using RTE_LOG */
#define RTE_LOGTYPE_REORDERAPP          RTE_LOGTYPE_USER1

#define NIPQUAD_FMT "%u.%u.%u.%u"
#define PRINT_IP(ip) printf("%u.%u.%u.%u", (ip) & 0xff , ((ip) >> 8) & 0xff, ((ip) >> 16) & 0xff, ((ip) >> 24) & 0xff)

#define PRINT_MAC(addr)		printf("%02"PRIx8":%02"PRIx8":%02"PRIx8 \
		":%02"PRIx8":%02"PRIx8":%02"PRIx8,	\
		(addr).addr_bytes[0], (addr).addr_bytes[1], (addr).addr_bytes[2], \
		(addr).addr_bytes[3], (addr).addr_bytes[4], (addr).addr_bytes[5])

volatile uint8_t quit_signal;

struct route_tuple;
struct output_buffer;
struct hdr_control_message;
struct create_control_message;
struct create_ack_control_message;
struct modify_control_message;
struct modify_ack_control_message;
struct nodify_control_message;
struct nodify_ack_control_message;

static struct rte_mempool *mbuf_pool;
static struct rte_eth_conf port_conf_default;
static struct rte_ring* ring_arp_reply;
static struct rte_ring* ring_arp_request; //for mac-ip learning
static struct rte_ring* ring_out_control;
static struct rte_ring* ring_session_id;

static struct rte_hash* hash_ip_to_mac_table;

static struct ether_addr mac_table[IP_TO_MAC_TABLE_SIZE];
static int has_mac[IP_TO_MAC_TABLE_SIZE] = { 0 };
static int check_arp_sent[IP_TO_MAC_TABLE_SIZE] = { 0 };

static int32_t is_setip_public_side[MAX_SESSION] = { 0 };
static int32_t is_auto_public[MAX_SESSION] = { 0 };
static int32_t is_setip_private_side[MAX_SESSION] = { 0 };
static int32_t is_active_session[MAX_SESSION] = { 0 };

static int32_t start_data_port = 8000;
static int32_t max_session = 52000;
static int32_t control_port = 7878;

static struct rte_mbuf* create_udp_packet(uint32_t pconf_id, void* data,
		uint32_t data_len, uint32_t s_port, uint32_t d_ip, uint32_t d_port);
static struct rte_mbuf* create_arp_packet(uint8_t portid, uint32_t sip,
		uint32_t tip);
static inline void pktmbuf_free_bulk(struct rte_mbuf *mbuf_table[], unsigned n);
static inline send_packet_imediately(struct rte_mbuf* m, uint8_t outp);
static inline int32_t validate_udp_packet(struct ipv4_hdr * ip_hdr,
		struct udp_hdr * udp_hdr);
static inline void flush_one_port(struct output_buffer *outbuf, uint8_t outp);

static void learn_mac_ip(struct ether_addr* mac, uint32_t ip);
static __inline__ void inetAddrCopy(void * t, void * f);
static __inline__ void inetAddrSwap(void * t, void * f);
static __inline__ void uint16Swap(void * t, void * f);
static __inline__ void ethAddrSwap(void * t, void * f);
static __inline__ uint32_t wrapsum(uint32_t sum);
static __inline__ uint32_t checksum(void *data, unsigned nbytes, uint32_t sum);

struct route_tuple {
	uint32_t ip;
	uint32_t port;
}__attribute__((__packed__));

static struct route_tuple route_public_side[MAX_SESSION];
static struct route_tuple route_private_side[MAX_SESSION];

struct hdr_control_message {
	uint32_t flag;
	uint32_t length;
	uint32_t message_id;
	uint32_t point_code_from;
	uint32_t point_code_to;
	uint32_t transaction_id;
	uint32_t rid;
	uint32_t ssrc;
};

struct create_control_message {
	struct hdr_control_message hdr;
	uint32_t public_ip;
	uint32_t public_port;
	uint32_t private_ip;
	uint32_t private_port;
	uint32_t auto_remote;
};

struct create_ack_control_message {
	struct hdr_control_message hdr;
	uint32_t id;
	uint32_t public_ip;
	uint32_t public_port;
	uint32_t private_ip;
	uint32_t private_port;
};

struct modify_control_message {
	struct hdr_control_message hdr;
	uint32_t public_ip;
	uint32_t public_port;
	uint32_t private_ip;
	uint32_t private_port;
	uint32_t auto_remote;
};

struct modify_ack_control_message {
	struct hdr_control_message hdr;
};

struct nodify_control_message {
	struct hdr_control_message hdr;
	uint32_t id;
	uint32_t public_ip;
	uint32_t public_port;
	uint32_t payload;
};

struct nodify_ack_control_message {
	struct hdr_control_message hdr;
};

struct output_buffer {
	unsigned count;
	struct rte_mbuf *mbufs[MAX_PKTS_BURST];
};

struct port_configure {
	uint8_t portid;
	struct rte_ring* ring_in;
	struct rte_ring* ring_out;
	struct output_buffer out_buf;
	struct ether_addr addr;
	uint32_t ip;
	uint32_t gw;
	uint32_t subnet_mask;
};

static uint16_t packet_indent = 0;
static int32_t num_config_port;
static struct port_configure ports_conf[RTE_MAX_ETHPORTS];

static void int_handler(int sig_num) {
	printf("Exiting on signal %d\n", sig_num);
	quit_signal = 1;
}

/* ethSwap(u16_t * to, u16_t * from) - Swap two 16 bit values */
static __inline__ void uint16Swap(void * t, void * f) {
	uint16_t * d = (uint16_t *) t;
	uint16_t * s = (uint16_t *) f;
	uint16_t v;
	v = *d;
	*d = *s;
	*s = v;
}

/* ethAddrSwap( u16_t * to, u16_t * from ) - Swap two ethernet addresses */
static __inline__ void ethAddrSwap(void * t, void * f) {
	uint16_t * d = (uint16_t *) t;
	uint16_t * s = (uint16_t *) f;
	uint16Swap(d++, s++);
	uint16Swap(d++, s++);
	uint16Swap(d, s);
}

/* inetAddrCopy( void * t, void * f ) - Copy IPv4 address */
static __inline__ void inetAddrCopy(void * t, void * f) {
	uint32_t * d = (uint32_t *) t;
	uint32_t * s = (uint32_t *) f;
	*d = *s;
}

/* inetAddrSwap( void * t, void * f ) - Swap two IPv4 addresses */
static __inline__ void inetAddrSwap(void * t, void * f) {
	uint32_t * d = (uint32_t *) t;
	uint32_t * s = (uint32_t *) f;
	uint32_t v;
	v = *d;
	*d = *s;
	*s = v;
}

static __inline__ uint32_t wrapsum(uint32_t sum) {
	sum = ~sum & 0xFFFF;
	return (htons(sum));
}

static __inline__ uint32_t checksum(void *data, unsigned nbytes, uint32_t sum) {
	uint32_t i = 0;
	unsigned char *buf = (unsigned char *) data;

	/* Checksum all the pairs of bytes first... */
	for (i = 0; i < (nbytes & ~1U); i += 2) {
		sum += (uint16_t) ntohs(*((uint16_t *) (buf + i)));
		if (sum > 0xFFFF)
			sum -= 0xFFFF;
	}

	/*
	 * If there's a single byte left over, checksum it, too.
	 * Network byte order is big-endian, so the remaining byte is
	 * the high byte.
	 */
	if (i < nbytes) {
		sum += buf[i] << 8;
		if (sum > 0xFFFF)
			sum -= 0xFFFF;
	}

	return (sum);
}

static inline uint32_t ipv4_hash_crc(const void *data,
__rte_unused uint32_t data_len, uint32_t init_val) {
	uint32_t ip = *((uint32_t *) data);
#ifdef RTE_MACHINE_CPUFLAG_SSE4_2
	init_val = rte_hash_crc_4byte(ip, init_val);
#else /* RTE_MACHINE_CPUFLAG_SSE4_2 */
	init_val = rte_jhash_1word(ip, init_val);
#endif /* RTE_MACHINE_CPUFLAG_SSE4_2 */        
	return (init_val);
}

static inline uint32_t route_tuple_hash(const void *data,
__rte_unused uint32_t data_len, uint32_t init_val) {
	struct route_tuple *route = ((struct route_tuple *) data);

#ifdef RTE_MACHINE_CPUFLAG_SSE4_2
	init_val = rte_hash_crc_4byte(route->ip, init_val);
	init_val = rte_hash_crc_4byte(route->port, init_val);
#else /* RTE_MACHINE_CPUFLAG_SSE4_2 */
	init_val = rte_jhash_1word(route->ip, init_val);
	init_val = rte_jhash_1word(route->port, init_val);
#endif /* RTE_MACHINE_CPUFLAG_SSE4_2 */

	return (init_val);
}

static inline void pktmbuf_free_bulk(struct rte_mbuf *mbuf_table[], unsigned n) {
	unsigned int i;
	for (i = 0; i < n; i++)
		rte_pktmbuf_free(mbuf_table[i]);
}

static int configure_eth_port(int32_t id) {

	struct port_configure* pconf = &ports_conf[id];

	struct ether_addr* addr = &pconf->addr;

	const uint16_t rxRings = 1, txRings = 1;
	const uint8_t nb_ports = rte_eth_dev_count();
	int ret;
	uint16_t q;
	int32_t port_id = pconf->portid;
	char buf[1024];
	pconf->out_buf.count = 0;

	if (port_id > nb_ports)
		return -1;

	ret = rte_eth_dev_configure(port_id, rxRings, txRings, &port_conf_default);

	if (ret != 0)
		return ret;

	for (q = 0; q < rxRings; q++) {
		ret = rte_eth_rx_queue_setup(port_id, q, RX_DESC_PER_QUEUE,
				rte_eth_dev_socket_id(port_id), NULL, mbuf_pool);
		if (ret < 0)
			return ret;
	}

	for (q = 0; q < txRings; q++) {
		ret = rte_eth_tx_queue_setup(port_id, q, TX_DESC_PER_QUEUE,
				rte_eth_dev_socket_id(port_id), NULL);
		if (ret < 0)
			return ret;
	}

	snprintf(buf, sizeof(buf), "ring_in_%d", port_id);
	pconf->ring_in = rte_ring_create(buf, RING_SIZE, rte_socket_id(),
	RING_F_SP_ENQ);
	if (pconf->ring_in == NULL) {
		return -1;
	}
	snprintf(buf, sizeof(buf), "ring_out_%d", port_id);
	pconf->ring_out = rte_ring_create(buf, RING_SIZE, rte_socket_id(),
	RING_F_SC_DEQ);
	if (pconf->ring_out == NULL) {
		return -1;
	}

	ret = rte_eth_dev_start(port_id);
	if (ret < 0)
		return ret;

	rte_eth_macaddr_get(port_id, addr);
	printf("Port %u MAC: %02"PRIx8" %02"PRIx8" %02"PRIx8
	" %02"PRIx8" %02"PRIx8" %02"PRIx8"\n", (unsigned) port_id,
			addr->addr_bytes[0], addr->addr_bytes[1], addr->addr_bytes[2],
			addr->addr_bytes[3], addr->addr_bytes[4], addr->addr_bytes[5]);

	rte_eth_promiscuous_enable(port_id);

	return 0;
}

#define MMENQUEUE(ring,m) {ret = rte_ring_enqueue_burst((ring), (void *)&(m), 1); 	if(unlikely(ret < 1)) {	rte_pktmbuf_free(m);}}
#define MMENQUEUE2(ring,m) {ret = rte_ring_enqueue_burst((ring), (void *)&(m), 1); 	if(unlikely(ret < 1)) {	rte_free(m);}}

static int rx_thread(void * param) {
	struct port_configure * pconf = NULL; //(struct port_configure *) param;
	struct rte_ring* ring_in = NULL; //pconf->ring_in;
	struct rte_ring* ring_out = NULL; //pconf->ring_out;
	uint8_t port_id = 0; //pconf->portid;
	uint16_t nb_rx_pkts;
	struct rte_mbuf *m;
	struct ether_hdr *eth_hdr;
	struct arp_hdr *arp_hdr;
	int32_t i, j, k, ret;
	struct rte_mbuf *pkts[MAX_PKTS_BURST];
	int32_t ether_type;
	struct ipv4_hdr *ip_hdr;
	struct icmp_hdr* icmp_hdr;
	struct udp_hdr* udp_hdr;

	while (!quit_signal) {
		for (k = 0; k < num_config_port; ++k) {
			pconf = &ports_conf[k];
			ring_in = pconf->ring_in;
			ring_out = pconf->ring_out;
			port_id = pconf->portid;

			nb_rx_pkts = rte_eth_rx_burst(port_id, 0, pkts, MAX_PKTS_BURST);

			if (unlikely(nb_rx_pkts == 0)) {
				continue;
			}

			for (i = 0; i < nb_rx_pkts; ++i) {
				m = pkts[i];
				eth_hdr = rte_pktmbuf_mtod(m, struct ether_hdr *);
				ether_type = eth_hdr->ether_type;

				if (unlikely(rte_cpu_to_be_16(ETHER_TYPE_ARP) == ether_type)) {

					arp_hdr = (struct arp_hdr *) ((char *) (eth_hdr + 1));

					if (arp_hdr->arp_op == rte_cpu_to_be_16(ARP_OP_REQUEST)) {
						if (arp_hdr->arp_data.arp_tip == (pconf->ip)) {
							arp_hdr->arp_op = rte_cpu_to_be_16(ARP_OP_REPLY);
							ether_addr_copy(&eth_hdr->s_addr, &eth_hdr->d_addr);
							ether_addr_copy(&pconf->addr, &eth_hdr->s_addr);
							ether_addr_copy(&arp_hdr->arp_data.arp_sha,
									&arp_hdr->arp_data.arp_tha);
							arp_hdr->arp_data.arp_tip =
									arp_hdr->arp_data.arp_sip;
							ether_addr_copy(&pconf->addr,
									&arp_hdr->arp_data.arp_sha);
							arp_hdr->arp_data.arp_sip = (pconf->ip);
							MMENQUEUE(ring_out, m);
						} else {
							MMENQUEUE(ring_arp_request, m);
						}
					} else if (arp_hdr->arp_op == rte_cpu_to_be_16(ARP_OP_REPLY)) {
						MMENQUEUE(ring_arp_reply, m);
					} else {
						rte_pktmbuf_free(m);
					}
				} else if (likely(
						rte_cpu_to_be_16(ETHER_TYPE_IPv4) == ether_type)) {
					ip_hdr = (struct ipv4_hdr *) ((char *) (eth_hdr + 1));
					switch (ip_hdr->next_proto_id) {
					case IPPROTO_ICMP:
						//printf("nhan ban tin ping\n");
						icmp_hdr = (struct icmp_hdr *) ((unsigned char *) ip_hdr
								+ sizeof(struct ipv4_hdr));

						if (unlikely(
								wrapsum(
										checksum(icmp_hdr,
												(m->data_len
														- sizeof(struct ether_hdr)
														- sizeof(struct ipv4_hdr)),
												0)))) {
							printf("ICMP check sum error\n");
							rte_pktmbuf_free(m);
							break;
						}

						if (unlikely(
								icmp_hdr->icmp_type == IP_ICMP_ECHO_REQUEST)) {
							if (ntohl(ip_hdr->dst_addr) == INADDR_BROADCAST) {
								rte_pktmbuf_free(m);
							} else {
								icmp_hdr->icmp_type = IP_ICMP_ECHO_REPLY;
								icmp_hdr->icmp_cksum = 0;
								icmp_hdr->icmp_cksum =
										wrapsum(
												checksum(icmp_hdr,
														(m->data_len
																- sizeof(struct ether_hdr)
																- sizeof(struct ipv4_hdr)),
														0));

								inetAddrSwap(&ip_hdr->src_addr,
										&ip_hdr->dst_addr);

								ip_hdr->packet_id = htons(
										ntohs(ip_hdr->packet_id) + m->data_len);

								ip_hdr->hdr_checksum = 0;
								ip_hdr->hdr_checksum = wrapsum(
										checksum(ip_hdr,
												sizeof(struct ipv4_hdr), 0));

								ethAddrSwap(&eth_hdr->d_addr, &eth_hdr->s_addr);
								MMENQUEUE(ring_out, m);
							}
						} else {
							rte_pktmbuf_free(m);
						}
						break;
					case IPPROTO_UDP:
						MMENQUEUE(ring_in, m)
						;
						break;

					default:
						rte_pktmbuf_free(m);
					}

				} else {
					rte_pktmbuf_free(m);
				}
			}
		}
	}

	return 0;
}

static inline send_packet_imediately(struct rte_mbuf* m, uint8_t outp) {
	unsigned nb_tx = rte_eth_tx_burst(outp, 0, &m, 1);
	if (unlikely(nb_tx < 1)) {
		rte_pktmbuf_free(m);
	}
}

static inline void flush_one_port(struct output_buffer *outbuf, uint8_t outp) {
	unsigned nb_tx = rte_eth_tx_burst(outp, 0, outbuf->mbufs, outbuf->count);
	if (unlikely(nb_tx < outbuf->count)) {
		pktmbuf_free_bulk(&outbuf->mbufs[nb_tx], outbuf->count - nb_tx);
	}
	outbuf->count = 0;
}

static inline int32_t validate_udp_packet(struct ipv4_hdr * ip_hdr,
		struct udp_hdr * udp_hdr) {
	uint16_t temp = 0;

	if (unlikely(wrapsum(checksum(ip_hdr, sizeof(struct ipv4_hdr), 0)) != 0)) //checksum ip_hdr fail
		return -1;

	temp = (udp_hdr->dgram_cksum);
	if (unlikely(temp == 0))
		return 0;

	udp_hdr->dgram_cksum = 0;

	udp_hdr->dgram_cksum = wrapsum(
			checksum((unsigned char *) udp_hdr, sizeof(struct udp_hdr),
					checksum(&udp_hdr[1],
							ntohs(ip_hdr->total_length)
									- sizeof(struct ipv4_hdr)
									- sizeof(struct udp_hdr),
							checksum((unsigned char *) &ip_hdr->src_addr,
									2 * sizeof(ip_hdr->src_addr),
									IPPROTO_UDP
											+ (uint32_t) ntohs(
													udp_hdr->dgram_len)))));

	if (unlikely(temp != udp_hdr->dgram_cksum)) // check sum udp fail
		return -2;

	return 0;
}

static int32_t process_control_message(uint8_t pconf_id, struct rte_mbuf* m,
		struct hdr_control_message * hdr) {
	uint32_t msgtype;

	struct port_configure * pconf = &ports_conf[pconf_id];
	struct rte_ring * ring_in = pconf->ring_in;
	struct rte_ring * ring_out = pconf->ring_out;
	uint8_t port_id = pconf->portid;
	struct rte_mbuf* mret = NULL;
	struct ether_hdr *eth_hdr = rte_pktmbuf_mtod(m, struct ether_hdr *);
	struct ipv4_hdr *ip_hdr = (struct ipv4_hdr *) &eth_hdr[1];
	struct udp_hdr * udp_hdr = (struct udp_hdr *) &ip_hdr[1];

//	uint32_t public_ip;
//	uint32_t public_port;
//	uint32_t private_ip;
//	uint32_t private_port;
//	uint32_t auto_remote;
	static struct create_control_message createmsg = { { .flag = 0, .length =
			sizeof(struct create_control_message), .message_id = 501,
			.point_code_from = 0, .point_code_to = 0, .transaction_id = 0,
			.rid = 0, .ssrc = 0 }, .public_ip = 0, .public_port = 0,
			.private_ip = 0, .private_port = 0, .auto_remote = 0 };

	static struct create_ack_control_message createackmsg = { { .flag = 0,
			.length = sizeof(struct create_ack_control_message), .message_id =
					502, .point_code_from = 0, .point_code_to = 0,
			.transaction_id = 0, .rid = 0, .ssrc = 0 }, .id = 0, .public_ip = 0,
			.public_port = 0, .private_ip = 0, .private_port = 0 };

	int32_t ret;
	uint16_t * idbuf[1];
	uint32_t nb_dq_id;
	uint32_t sid;
	uint32_t session_id;

	msgtype = hdr->message_id;
	createackmsg.hdr.message_id = 502;
	createackmsg.hdr.length = sizeof(createackmsg);

	switch (msgtype) {
	case 501: {
		memcpy(&createmsg, hdr, sizeof(struct create_control_message));
		nb_dq_id = rte_ring_dequeue_burst(ring_session_id, (void *) idbuf, 1);
		if (likely(nb_dq_id == 1)) {
			sid = *idbuf[0];
			session_id = sid - start_data_port;

			is_active_session[session_id] = 1;

			if (createmsg.auto_remote != 0) {
				is_auto_public[session_id] = 1;
			}
			rte_free(idbuf[0]);

			if (createmsg.public_ip != CTRL_MSG_INVALID
					&& createmsg.public_port != CTRL_MSG_INVALID) {
				if (createmsg.auto_remote != 0) {
					is_setip_public_side[session_id] = 1;
					route_public_side[session_id].ip = createmsg.public_ip;
					route_public_side[session_id].ip = createmsg.public_port;
				} else {
					is_setip_public_side[session_id] = 0;
				}
			} else {
				is_setip_public_side[session_id] = 0;
			}

			if (createmsg.private_ip != CTRL_MSG_INVALID
					&& createmsg.private_port != CTRL_MSG_INVALID) {
				is_setip_private_side[session_id] = 1;
				route_private_side[session_id].ip = createmsg.private_ip;
				route_private_side[session_id].ip = createmsg.private_port;
			} else {
				is_setip_private_side[session_id] = 1;
			}

			createackmsg.id = session_id;
			createackmsg.private_ip = ports_conf[1].ip;
			createackmsg.private_port = sid;
			createackmsg.public_ip = ports_conf[0].ip;
			createackmsg.public_port = sid;

			mret = create_udp_packet(pconf_id, &createackmsg,
					sizeof(createackmsg), ntohs(udp_hdr->dst_port),
					ip_hdr->src_addr, ntohs(udp_hdr->src_port));

			if (mret != NULL) {
				MMENQUEUE(ring_out, mret);
			}

		} else {
			createackmsg.id = CTRL_MSG_INVALID;
			mret = create_udp_packet(pconf_id, &createackmsg,
					sizeof(createackmsg), ntohs(udp_hdr->dst_port),
					ip_hdr->src_addr, ntohs(udp_hdr->src_port));

			if (mret != NULL) {
				MMENQUEUE(ring_out, mret);
			}

		}
	}
		rte_pktmbuf_free(m);
		break;

	default:
		rte_pktmbuf_free(m);
		break;
	}

	return 0;
}

static int32_t process_packet_from_internal_side(uint8_t pconf_id,
		struct rte_mbuf* m) {
	int32_t i, j, k, ret;
	struct ether_hdr *eth_hdr = rte_pktmbuf_mtod(m, struct ether_hdr *);
	struct ipv4_hdr *ip_hdr = (struct ipv4_hdr *) &eth_hdr[1];
	struct udp_hdr * udp_hdr = (struct udp_hdr *) &ip_hdr[1];

	ret = validate_udp_packet(ip_hdr, udp_hdr);

	if (unlikely(ret != 0)) {
		rte_pktmbuf_free(m);
		return -1;
	}

	if (unlikely(ntohs(udp_hdr->dst_port) == control_port)) {
		process_control_message(pconf_id, m,
				(struct hdr_control_message *) &udp_hdr[1]);
	}

	return 0;
}

static void process_packet_from_public_side(struct rte_mbuf* m,
		struct ipv4_hdr* ip, struct udp_hdr* udp) {
	int32_t i, j, k, ret;
	uint32_t port = ntohs(udp->dst_port);
	uint32_t session_id = port - session_id;
	static struct route_tuple* route_tuple;
	struct port_configure * port_pub = &ports_conf[0];
	struct port_configure * port_private = &ports_conf[1];

	if (unlikely(session_id >= MAX_SESSION)) {
		rte_pktmbuf_free(m);
		return;
	}

	if (unlikely(is_active_session[session_id] == 0)) {
		rte_pktmbuf_free(m);
		return;
	}
	route_tuple = &route_private_side[session_id];
	if (likely(is_setip_private_side[session_id] != 0)) {
		udp->dst_port = htons(route_tuple->port);
		ip->dst_addr = route_tuple->ip;
		udp->src_port = htons(session_id + start_data_port);
		ip->src_addr = port_private->ip;
		udp->dgram_cksum = 0;
		udp->dgram_cksum = wrapsum(checksum(ip, ip->total_length, 0));
	} else {
		rte_pktmbuf_free(m);
		return;
	}
}

static int work_thread(void* param) {

	struct port_configure * pconf = NULL; //(struct port_configure *) param;
	struct rte_ring* ring_in = NULL; //pconf->ring_in;
	struct rte_ring* ring_out = NULL; //pconf->ring_out;
	uint8_t port_id = 0; //pconf->portid;
	struct ether_hdr *eth_hdr;
	struct arp_hdr *arp_hdr;
	int32_t i, j, k, ret;
	struct rte_mbuf *mbufs[MAX_PKTS_BURST];
	struct rte_mbuf * m;
	uint16_t nb_dq_mbufs;
	int32_t ether_type;
	struct ipv4_hdr *ip_hdr;
	struct icmp_hdr* icmp_hdr;
	struct udp_hdr* udp_hdr;

	const uint64_t drain_tsc = (rte_get_tsc_hz() + US_PER_S - 1) / US_PER_S
			* TIMER_1SEC_DRAIN_US;

	uint64_t prev_tsc = 0, diff_tsc = 0, cur_tsc = 0, timer_tsc = 0;

	for (i = start_data_port; i < start_data_port + max_session; ++i) {
		uint16_t * psid = NULL;
		psid = (uint16_t *) rte_malloc("uint16_t_session_id", sizeof(uint16_t),
				0);
		if (psid == NULL) {
			rte_exit(EXIT_FAILURE, "Error: can not insert session id to queue");
		}
		*psid = (uint16_t) i;
		MMENQUEUE2(ring_session_id, psid);
	}

	while (!quit_signal) {
		cur_tsc = rte_rdtsc();
		diff_tsc = cur_tsc - prev_tsc;
		if (unlikely(diff_tsc > drain_tsc)) {

			prev_tsc = cur_tsc;
		}

		for (k = 0; k < num_config_port; ++k) {

			pconf = &ports_conf[k];
			ring_in = pconf->ring_in;
			ring_out = pconf->ring_out;
			port_id = pconf->portid;

			nb_dq_mbufs = rte_ring_dequeue_burst(ring_out, (void *) mbufs,
			MAX_PKTS_BURST);

			if (unlikely(nb_dq_mbufs == 0)) {
				continue;
			}

			for (i = 0; i < nb_dq_mbufs; ++i) {
				m = mbufs[i];
				eth_hdr = rte_pktmbuf_mtod(m, struct ether_hdr *);
				ip_hdr = (struct ipv4_hdr *) &eth_hdr[1];
				udp_hdr = (struct udp_hdr *) &ip_hdr[1];

				switch (k) {
				case 0: //public port
					//process_packet_from_public_side(m , ip_hdr, udp_hdr);
					break;
				case 1: //internal port

					break;
				default:
					break;
				}
			}
		}
	}
	return 0;
}

static struct rte_mbuf* create_udp_packet(uint32_t pconf_id, void* data,
		uint32_t data_len, uint32_t s_port, uint32_t d_ip, uint32_t d_port) {
	struct port_configure* pconf = &ports_conf[pconf_id];
	struct rte_mbuf* m = NULL;
	struct ether_hdr * eth = NULL;
	struct ipv4_hdr * ip_hdr = NULL;
	struct udp_hdr * udp_hdr = NULL;
	unsigned char* buf = NULL;

	m = rte_pktmbuf_alloc(mbuf_pool);
	if (unlikely(m == NULL))
		return NULL;

	eth = rte_pktmbuf_mtod(m, struct ether_hdr *);

	ip_hdr = (struct ipv4_hdr *) &eth[1];
	udp_hdr = (struct udp_hdr *) &ip_hdr[1];

	buf = (unsigned char *) &udp_hdr[1];
	memcpy(buf, data, data_len);

	eth->ether_type = htons(ETHER_TYPE_IPv4);
	memset(ip_hdr, 0, sizeof(struct ipv4_hdr));
	memset(udp_hdr, 0, sizeof(struct udp_hdr));
	ether_addr_copy(&pconf->addr, &eth->s_addr);

	ip_hdr->version_ihl = (IPv4_VERSION << 4) | (sizeof(struct ipv4_hdr) / 4);
	ip_hdr->total_length = htons(
			data_len + sizeof(struct ipv4_hdr) + sizeof(struct udp_hdr));
	ip_hdr->time_to_live = 255;
	ip_hdr->type_of_service = 0;

	packet_indent += 27;

	ip_hdr->packet_id = htons(packet_indent);
	ip_hdr->fragment_offset = 0;
	ip_hdr->next_proto_id = (IPPROTO_UDP);

	ip_hdr->src_addr = pconf->ip;
	ip_hdr->dst_addr = d_ip;
	ip_hdr->hdr_checksum = wrapsum(
			checksum((unsigned char *) ip_hdr, sizeof(struct ipv4_hdr), 0)); //cksum(ip_hdr, sizeof(struct ipv4_hdr), 0);
	udp_hdr->src_port = htons(s_port);
	udp_hdr->dst_port = htons(d_port);
	udp_hdr->dgram_len = htons(data_len + sizeof(struct udp_hdr));

	//udp_hdr->dgram_cksum = 0;
	// udp_hdr->dgram_cksum = checksum(ip_hdr , ntohs(ip_hdr->total_length) , 0);
	// if(unlikely(udp_hdr->dgram_cksum == 0 )) {
	// 	udp_hdr->dgram_cksum = 0xFFFF;
	// }

	udp_hdr->dgram_cksum = wrapsum(
			checksum((unsigned char *) udp_hdr, sizeof(struct udp_hdr),
					checksum(data, data_len,
							checksum((unsigned char *) &ip_hdr->src_addr,
									2 * sizeof(ip_hdr->src_addr),
									IPPROTO_UDP
											+ (uint32_t) ntohs(
													udp_hdr->dgram_len)))));

	m->pkt_len = sizeof(struct ether_hdr) + sizeof(struct ipv4_hdr)
			+ sizeof(struct udp_hdr) + data_len;
	m->data_len = m->pkt_len;

	return m;
}

static struct rte_mbuf* create_arp_packet(uint8_t portid, uint32_t sip,
		uint32_t tip) {
	struct rte_mbuf* m = NULL;
	struct ether_hdr * eth;
	struct arp_hdr * arp;

	m = rte_pktmbuf_alloc(mbuf_pool);
	if (unlikely(m == NULL))
		return NULL;

	eth = rte_pktmbuf_mtod(m, struct ether_hdr *);
	arp = (struct arp_hdr *) &eth[1];
	memset(&eth->d_addr, 0xFF, 6);

	rte_eth_macaddr_get(portid, &eth->s_addr);
	eth->ether_type = htons(ETHER_TYPE_ARP);
	memset(arp, 0, sizeof(struct arp_hdr));
	ether_addr_copy(&eth->s_addr, &arp->arp_data.arp_sha);

	arp->arp_data.arp_sip = sip;
	arp->arp_data.arp_tip = tip;

	arp->arp_hrd = htons(RTE_PTYPE_L2_ETHER);
	arp->arp_pro = htons(ETHER_TYPE_IPv4);
	arp->arp_hln = 6;
	arp->arp_pln = 4;
	arp->arp_op = htons(ARP_OP_REQUEST);
	m->pkt_len = 60;
	m->data_len = 60;
	return m;
}

static void learn_mac_ip(struct ether_addr* mac, uint32_t ip) {
	int32_t ret;
	if (ntohl(ip) != INADDR_BROADCAST) {
		printf("Learned mac-ip: ");
		PRINT_MAC((*mac));
		printf(" ");
		PRINT_IP(ip);
		printf("\n");
		fflush(stdout);

		ret = rte_hash_lookup(hash_ip_to_mac_table, (void*) &ip);
		if (ret >= 0) {
			ether_addr_copy(mac, &mac_table[ret]);
			has_mac[ret] = 1;
		} else {
			ret = rte_hash_add_key(hash_ip_to_mac_table, (void*) &ip);
			if (likely(ret >= 0)) {
				ether_addr_copy(mac, &mac_table[ret]);
				has_mac[ret] = 1;
			}
		}
	}
}

static inline int32_t fill_mac(struct rte_mbuf* m, uint32_t ip,
		uint16_t port_id, struct ether_hdr* eth_hdr,
		struct port_configure* pconf) {
	int32_t ret = rte_hash_lookup(hash_ip_to_mac_table, (void*) &ip);
	if (likely((ret >= 0) && (has_mac[ret] != 0))) {
		ether_addr_copy(&mac_table[ret], &eth_hdr->d_addr);
		return 0;
	} else {
		rte_pktmbuf_free(m);
		if (unlikely(ret < 0)) {
			ret = rte_hash_add_key(hash_ip_to_mac_table, (void*) &ip);
			if (unlikely(ret < 0)) {
				printf("MAC table is full!\n");
				return 1;
			}
		}
		if (likely(check_arp_sent[ret] == 0)) {
			printf("Send arp request for ip ");
			PRINT_IP(ip);
			printf("\n");
			m = create_arp_packet(port_id, pconf->ip, ip);
			if (likely(m != NULL)) {
				send_packet_imediately(m, port_id);
			}
			check_arp_sent[ret] = 1;
		} else {
			//printf("check_arp_sent[%d] = %u", ret, check_arp_sent[ret]);
		}

		return 2;
	}
}

static int tx_thread(void* param) {
	const uint64_t drain_tsc = (rte_get_tsc_hz() + US_PER_S - 1) / US_PER_S
			* TIMER_1SEC_DRAIN_US;
	const uint64_t drain_1militsc = (rte_get_tsc_hz() + US_PER_S - 1) / US_PER_S
			* TIMER_1MILISEC_DRAIN_US;

	struct rte_mbuf *mbufs[MAX_PKTS_BURST];
	int32_t ret, i, j, k;
	uint16_t nb_dq_mbufs;
	struct port_configure * pconf = NULL; //(struct port_configure *) param;
	struct rte_ring* ring_out = NULL; //pconf->ring_out;
	struct output_buffer *outbuf;
	int8_t port_id;
	struct rte_mbuf *m;
	struct ether_hdr *eth_hdr;
	struct arp_hdr *arp_hdr;
	struct ipv4_hdr *ip_hdr;
	struct udp_hdr *udp_hdr;
	uint32_t ip;
	uint64_t prev_tsc = 0, diff_tsc = 0, cur_tsc = 0, timer_tsc = 0,
			prev_tsc_sent = 0;
	struct create_control_message msg;

	memset(&msg, 0, sizeof(msg));
	msg.hdr.message_id = 501;

	//sent arp to gw
	for (k = 0; k < num_config_port; ++k) {
		pconf = &ports_conf[k];
		port_id = pconf->portid;
		m = create_arp_packet(port_id, pconf->ip, pconf->gw);
		if (m != NULL) {
			send_packet_imediately(m, port_id);
		}
	}

	while (!quit_signal) {
		cur_tsc = rte_rdtsc();
		diff_tsc = cur_tsc - prev_tsc;

		if (unlikely(diff_tsc > drain_tsc)) {
			struct in_addr inp;
			pconf = &ports_conf[0];
			ring_out = pconf->ring_out;
			port_id = pconf->portid;
			inet_aton("10.61.63.13", &inp);

			for (i = 0; i < IP_TO_MAC_TABLE_SIZE; ++i)
				check_arp_sent[i] = 0;

			msg.hdr.message_id++;
			m = create_udp_packet(0, "emha", 5, 21321, inp.s_addr, 23115);
			MMENQUEUE(ring_out, m);
			prev_tsc = cur_tsc;
		}

		for (k = 0; k < num_config_port; ++k) {
			pconf = &ports_conf[k];
			ring_out = pconf->ring_out;
			port_id = pconf->portid;
			outbuf = &pconf->out_buf;

			nb_dq_mbufs = rte_ring_dequeue_burst(ring_out, (void *) mbufs,
			MAX_PKTS_BURST);

			if (unlikely(nb_dq_mbufs == 0))
				continue;
			else {
				for (i = 0; i < nb_dq_mbufs; ++i) {
					m = mbufs[i];
					eth_hdr = rte_pktmbuf_mtod(m, struct ether_hdr *);
					/*Uu tien ban tin ARP duoc day di truoc*/
					if (unlikely(
							rte_cpu_to_be_16(ETHER_TYPE_ARP) == eth_hdr->ether_type)) {
						//mac ip learning
						arp_hdr = (struct arp_hdr *) ((char *) (eth_hdr + 1));
						ip = arp_hdr->arp_data.arp_tip;
						learn_mac_ip(&arp_hdr->arp_data.arp_tha, ip);
					}
					/*Uu tien ban tin ICMP duoc day di truoc*/
					if (likely(
							rte_cpu_to_be_16(ETHER_TYPE_IPv4) == eth_hdr->ether_type)) {
						ip_hdr = (struct ipv4_hdr *) (&eth_hdr[1]);
						if (likely((ip_hdr->next_proto_id) == IPPROTO_UDP)) {
							udp_hdr = (struct udp_hdr *) &ip_hdr[1];
							ip = ip_hdr->dst_addr;

							if (likely(
									(pconf->subnet_mask & ip)
											== (pconf->subnet_mask & pconf->ip))) { //ban tin gui di cung dai mang
								ret = fill_mac(m, ip, port_id, eth_hdr, pconf);
								if (unlikely(ret != 0))
									continue;
							} else { //ban tin gui ra ngoai mang
								ip = pconf->gw;
								ret = fill_mac(m, ip, port_id, eth_hdr, pconf);
								if (unlikely(ret != 0))
									continue;
							}
						}
					}

					outbuf->mbufs[outbuf->count++] = mbufs[i];
					diff_tsc = cur_tsc - prev_tsc_sent;
					if (unlikely(
							(outbuf->count == MAX_PKTS_BURST || (diff_tsc > drain_1militsc)))) {
						flush_one_port(outbuf, port_id);
						prev_tsc_sent = cur_tsc;
					}
				}
			}
		}

		nb_dq_mbufs = rte_ring_dequeue_burst(ring_arp_reply, (void *) mbufs,
		MAX_PKTS_BURST);
		if (likely(nb_dq_mbufs == 0))
			continue;
		else {
			for (i = 0; i < nb_dq_mbufs; ++i) {
				m = mbufs[i];
				eth_hdr = rte_pktmbuf_mtod(m, struct ether_hdr *);
				arp_hdr = (struct arp_hdr *) ((char *) (eth_hdr + 1));
				ip = ((uint32_t) arp_hdr->arp_data.arp_sip);
				learn_mac_ip(&arp_hdr->arp_data.arp_sha, ip);
				rte_pktmbuf_free(m);
			}
		}

		nb_dq_mbufs = rte_ring_dequeue_burst(ring_arp_request, (void *) mbufs,
		MAX_PKTS_BURST);
		if (likely(nb_dq_mbufs == 0))
			continue;
		else {
			for (i = 0; i < nb_dq_mbufs; ++i) {
				m = mbufs[i];
				eth_hdr = rte_pktmbuf_mtod(m, struct ether_hdr *);
				arp_hdr = (struct arp_hdr *) ((char *) (eth_hdr + 1));
				ip = ((uint32_t) arp_hdr->arp_data.arp_sip);
				learn_mac_ip(&arp_hdr->arp_data.arp_sha, ip);
				rte_pktmbuf_free(m);
			}
		}
	}
	return 0;
}

static void read_port_configure(int port_idx, FILE* pfile) {
	char buf[MAX_BUF];
	struct in_addr inp;
	struct port_configure *pconf = &ports_conf[port_idx];
	int32_t ret = 0;

	while (fscanf(pfile, "%s", buf) > 0) {
		if (strcmp(buf, "end") == 0)
			break;
		else if (strcmp(buf, "ip") == 0) {
			ret = fscanf(pfile, "%s", buf);
			inet_aton(buf, &inp);
			pconf->ip = inp.s_addr;
		} else if (strcmp(buf, "gw") == 0) {
			ret = fscanf(pfile, "%s", buf);
			inet_aton(buf, &inp);
			pconf->gw = inp.s_addr;
		} else if (strcmp(buf, "mask") == 0) {
			ret = fscanf(pfile, "%s", buf);
			inet_aton(buf, &inp);
			pconf->subnet_mask = inp.s_addr;
		} else if (strcmp(buf, "portid") == 0) {
			ret = fscanf(pfile, "%s", buf);

			pconf->portid = atoi(buf);
		}
	}
}

static void read_configure(void) {
	FILE *pfile = NULL;
	int32_t ret;
	pfile = fopen("gw.conf", "r");
	if (pfile) {
		int i;
		ret = fscanf(pfile, "%d", &num_config_port);
		for (i = 0; i < num_config_port; ++i) {
			read_port_configure(i, pfile);
		}
		fclose(pfile);
	} else {
		rte_exit(EXIT_FAILURE, "Error: can not find gw.conf file\n");
	}
}

int main(int argc, char **argv) {

	unsigned int lcore_id, last_lcore_id, master_lcore_id;
	int ret, nb_ports;
	int i = 0, j = 0;
	char buf[1024];

	quit_signal = 0;
	signal(SIGINT, int_handler);

	ret = rte_eal_init(argc, argv);
	if (ret < 0)
		return -1;

	argc -= ret;
	argv += ret;

	nb_ports = rte_eth_dev_count();
	/*if (nb_ports < 2)
	 rte_exit(EXIT_FAILURE, "Error: not enought ethernet ports detected\n");*/

	mbuf_pool = rte_pktmbuf_pool_create("mbuf_pool", MBUF_PER_POOL,
	MBUF_POOL_CACHE_SIZE, 0, RTE_MBUF_DEFAULT_BUF_SIZE, rte_socket_id());

	if (mbuf_pool == NULL)
		rte_exit(EXIT_FAILURE, "%s\n", rte_strerror(rte_errno));

	read_configure();

	struct rte_hash_parameters ip_to_mac_hash_params =
			{ .name = "hash_ip_to_mac_table", .entries = IP_TO_MAC_TABLE_SIZE,
					.key_len = sizeof(int32_t), .hash_func = ipv4_hash_crc,
					.hash_func_init_val = 0, };

	ip_to_mac_hash_params.socket_id = rte_socket_id();

	hash_ip_to_mac_table = rte_hash_create(&ip_to_mac_hash_params);
	if (hash_ip_to_mac_table == NULL)
		rte_exit(EXIT_FAILURE, "Can not create hash ip_to_mac on socket %d\n",
				rte_socket_id());

	for (i = 0; i < num_config_port; ++i) {
		ret = configure_eth_port(i);
		if (ret != 0)
			rte_exit(EXIT_FAILURE, "Error: configure port error %d\n", i);
	}

	ring_arp_reply = rte_ring_create("ring_arp_reply", 1024, rte_socket_id(),
	RING_F_SC_DEQ);
	if (ring_arp_reply == NULL) {
		rte_exit(EXIT_FAILURE, "Error: can not create ring_arp_reply");
	}

	ring_arp_request = rte_ring_create("ring_arp_request", 1024,
			rte_socket_id(), RING_F_SC_DEQ);
	if (ring_arp_request == NULL) {
		rte_exit(EXIT_FAILURE, "Error: can not create ring_arp_reply");
	}

	ring_out_control = rte_ring_create("ring_out_control", 1024,
			rte_socket_id(), RING_F_SC_DEQ);
	if (ring_out_control == NULL) {
		rte_exit(EXIT_FAILURE, "Error: can not create ring_out_control");
	}

	ring_session_id = rte_ring_create("ring_session_id", max_session,
			rte_socket_id(), RING_F_SC_DEQ);
	if (ring_session_id == NULL) {
		rte_exit(EXIT_FAILURE, "Error: can not create ring_session_id");
	}

	master_lcore_id = rte_get_master_lcore();
	for (lcore_id = 0, j = 0; lcore_id < RTE_MAX_LCORE; ++lcore_id)
		if ((lcore_id != master_lcore_id) && rte_lcore_is_enabled(lcore_id)) {
			if (j == 0) {
				rte_eal_remote_launch(rx_thread, NULL, lcore_id);
				printf("Start rx_thread on lcore_id %d\n", lcore_id);
				fflush(stdout);
			} else if (j == 1) {
				rte_eal_remote_launch(tx_thread, NULL, lcore_id);
				printf("Start tx_thread on lcore_id %d\n", lcore_id);
				fflush(stdout);
			}
			j++;
		}
	work_thread(NULL);
	RTE_LCORE_FOREACH_SLAVE(lcore_id)
	{
		if (rte_eal_wait_lcore(lcore_id) < 0)
			return -1;
	}
	return 0;
}
