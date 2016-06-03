! Copyright (C) 2005, 2009 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel io ;
in: io.streams.plain

mixin: plain-writer

M: plain-writer stream-nl
    CHAR: \n swap stream-write1 ;
