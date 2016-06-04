! Copyright (C) 2008 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: io.encodings.binary io.streams.byte-array kernel
checksums ;
in: checksums.stream

mixin: stream-checksum

M: stream-checksum checksum-bytes
    [ binary <byte-reader> ] dip checksum-stream ;

INSTANCE: stream-checksum checksum ;
