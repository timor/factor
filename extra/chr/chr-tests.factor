USING: chr chr.parser chr.state linked-assocs math tools.test ;
IN: chr.tests


TUPLE: gcd < chr-pred val ;
C: <gcd> gcd

TERM-VARS: ?i ?j ;

! TODO Test with symbolic leq
CONSTANT: gcd-ex {
CHR: gcd1 @ // { gcd ?i } -- [ ?i 0 == ] | true ;
CHR: gcd2 @ { gcd ?i } // { gcd ?j } -- [ ?j ?i >= ] | [ ?j ?i - <gcd> ] ;
}


{
    LH{ { 3 P{ gcd 3 } } }
}
[ gcd-ex { { gcd 6 } { gcd 9 } } run-chr-query ] unit-test
