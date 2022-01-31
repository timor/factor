USING: chr match sequences tools.test ;
IN: chr.tests


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

{ t }
[ leq-ex third propagate-chr? ] unit-test

{ f }
[ leq-ex first propagate-chr? ] unit-test

{
    { { leq A B } { leq B C } { leq C A } }
    { { leq A C } }
}
[ [ leq-ex third { { leq A B } { leq B C } { leq C A } } try-rule-match ] with-chr-trace
] unit-test

{
    { { leq A B } { leq B C } { leq C A } }
    { { leq A C } }
    { { leq A B } { leq B C } { leq C A } }
    f
}
[ [ leq-ex third { { leq A B } { leq B C } { leq C A } } try-rule-match
    leq-ex third { { leq A B } { leq B C } { leq C A } } try-rule-match ] with-chr-trace
] unit-test
