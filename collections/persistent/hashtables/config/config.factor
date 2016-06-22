! Copyright (C) 2008 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: layouts kernel parser math math.bitwise sequences
literals ;
IN: persistent.hashtables.config

CONSTANT: radix-bits $[ cell 4 = 4 5 ? ] ;
: radix-mask ( -- n ) radix-bits on-bits ; foldable
: full-bitmap-mask ( -- n ) radix-bits 2^ on-bits ; inline
