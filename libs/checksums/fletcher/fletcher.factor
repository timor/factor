! Copyright (C) 2013 John Benediktsson
! See http://factorcode.org/license.txt for BSD license

USING: checksums grouping io.binary kernel locals math sequences
;

IN: checksums.fletcher

SINGLETON: fletcher-16
SINGLETON: fletcher-32
SINGLETON: fletcher-64

INSTANCE: fletcher-16 checksum
INSTANCE: fletcher-32 checksum
INSTANCE: fletcher-64 checksum

:: fletcher ( seq k -- n )
    k 16 / set: chars
    k 2 / 2^ set: base
    base 1 - set: modulo
    0 0 seq chars <groups> [
        be> + modulo mod [ + modulo mod ] keep
    ] each [ base * ] [ + ] bi* ; inline

M: fletcher-16 checksum-bytes drop 16 fletcher ;
M: fletcher-32 checksum-bytes drop 32 fletcher ;
M: fletcher-64 checksum-bytes drop 64 fletcher ;
