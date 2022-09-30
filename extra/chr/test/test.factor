USING: continuations kernel sequences terms tools.test.private ;

IN: chr.test

: assert-isomorphic ( term1 term2 -- )
    2dup isomorphic? [ 2drop ] [ assert ] if ;

! Tests if the result of the quot is isomorphic to the given test input
! Note that this is NOT order-independent at the moment
:: (chr-test) ( output input -- error/f failed? tested? )
    [ { } input with-datastack first output assert-isomorphic f f ] [ t ] recover t ;

TEST: chr-test
