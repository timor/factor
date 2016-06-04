! Copyright (C) 2013 John Benediktsson
! See http://factorcode.org/license.txt for BSD license

USING: alien.c-types alien.syntax kernel random ;

in: random.c

library: libc

FUNCTION: int rand ( ) ;

singleton: c-random

M: c-random random-32* drop rand ;

: with-c-random ( quot -- )
    [ c-random ] dip with-random ; inline
