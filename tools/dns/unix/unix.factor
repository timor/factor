! Copyright (C) 2010 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors dns resolv-conf system ;
in: dns.unix

M: unix initial-dns-servers
    default-resolv.conf nameserver>> ;
