USING: chr chr.refined logic match tools.test ;

MATCH-VARS: ?x ?y ?z ;
SYMBOLS: A B C ;
SINGLETON: leq

! H_keep \ H_remove => G | B
! CONSTANT: leq-ex {
!     T{ chr { remove { { leq ?x ?y } } } { guard { T{ eq f ?x ?y } } } { body t } }
!     T{ chr { remove { { leq ?x ?y } { leq ?y ?x } } } { body { T{ eq f ?x ?y } } } }
!     T{ chr { keep { { leq ?x ?y } { leq ?y ?z } } } { body { { leq ?x ?z } } } }
!     ! T{ chr { keep { leq ?x ?y } } { remove { leq ?x ?y } } }
! }

CONSTANT: leq-ex {
    CHR{ // { leq ?x ?y } -- ={ ?x ?y } | }
    CHR{ // { leq ?x ?y } { leq ?y ?x } -- | ={ ?x ?y } }
    CHR{ { leq ?x ?y } { leq ?y ?z } // -- | { leq ?x ?z } }
    ! CHR{ { leq ?x ?y } // { leq ?x ?y } -- | }
}

{ { }
  { ={ A B } ={ C B } } }
[ leq-ex { { leq A B } { leq B C } { leq C A } } chr-run-refined ] unit-test

MATCH-VARS: ?i ?j ?k ;
SINGLETON: gcd
CONSTANT: gcd-prog {
    CHR{ // { gcd 0 } -- | }
    CHR{ { gcd ?i } // { gcd ?j } -- [ ?j ?i >= ] |
         !={ ?k [ ?j ?i - ] }
         { gcd ?k }
       }
}

{ { { gcd 3 } } f }
[ gcd-prog { { gcd 6 } { gcd 9 } } chr-run-refined ] unit-test

{ { { gcd 3 } } f }
[ gcd-prog { { gcd 9 } { gcd 6 } } chr-run-refined ] unit-test

{ { { gcd 1 } } f }
[ gcd-prog { { gcd 11 } { gcd 13 } } chr-run-refined ] unit-test
