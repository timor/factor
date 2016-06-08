USING: kernel math accessors random ;
in: random.dummy

TUPLE: random-dummy i ;
C: <random-dummy> random-dummy

M: random-dummy seed-random
    >>i ;

M: random-dummy random-32*
    [ dup 1 + ] change-i drop ;
