USING: accessors chr chr.parser chr.state kernel linked-assocs math tools.test ;
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

TERM-VARS: ?x ?y ?z ;

CONSTANT: var-test {
    CHR{ { = ?x ?y } // -- | { = ?z ?y } }
    CHR{ // { = ?x ?y } -- | { = ?y ?x } }
}

{ { ?x ?y ?z } { { ?z } {  } } }
[ var-test load-chr [ local-vars>> ] [ existential-vars>> ] bi ] unit-test


! For now, we don't support existential guards, only existential bodies
CONSTANT: invalid-test {
    CHR{ { = ?x ?y } // -- { = ?y ?z } | true }
}

[ invalid-test load-chr ] [ existential-guard-vars? ] must-fail-with
