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
         is={ ?k [ ?j ?i - ] }
         { gcd ?k }
       }
}

{ { { gcd 3 } } f }
[ gcd-prog { { gcd 6 } { gcd 9 } } chr-run-refined ] unit-test

{ { { gcd 3 } } f }
[ gcd-prog { { gcd 9 } { gcd 6 } } chr-run-refined ] unit-test

{ { { gcd 1 } } f }
[ gcd-prog { { gcd 11 } { gcd 13 } } chr-run-refined ] unit-test

! Passing Stuff via stack?
SYMBOLS: Stack State Word Before After Conn In Out Defs Def Comp Push Pop ShiftPop
    ShiftPush Unshift Prim Call Use ;
SYMBOLS: StartInfer Start Infer Infer1 Return Retval Param ;
MATCH-VARS: ?a ?b ?c ?r ?s ?s1 ?s2 ?s3 ?t ?u ?v ?w ?n ?m ?l ?d ?e ?q ;
TUPLE: var name ; C: <var> var
: <uvar> ( name -- var )
    uvar <var>
    ;
! INSTANCE: var match-var
! Not a match var, but needs to be considered for reactivation
M: var child-atoms drop f ;

: make-next-state ( sname -- sname )
    uvar ;
! Shift is a parallel constraint, which connects all undefined in/outs below a certain level
! Transitions are atomic and well ordered
! swap: [ { Pop s0 ?a } { Pop s1 ?b } { Push s2 ?a } { Push s3 ?b } ]
! GENERIC: >chr-cons ( word -- rule/f )
! M: \ swap >chr-cons
!     CHR{  }
!     ! { { ?a ?b } CHR{ { State ?n 0 ?a } { State ?n 1 ?b } // -- | [ ?n 1 + ] } }
! Shift{ prev next cut_in shift-by }
CONSTANT: stack-ex {
    ! Connection
    ! CHR{ { Out ?s ?n ?a } // { In ?s ?n ?b } -- | ={ ?b ?a } }
    ! Keep single source
    ! CHR{ { State ?s ?n ?a } // { State ?s ?n ?b } -- | ={ ?b ?a } }
    CHR{ { State ?s ?n ?a } // { State ?s ?n ?b } -- | ={ ?a ?b } }
    CHR{ // { Word ?s ?t swap } -- |
         is={ ?a [ "a" <uvar> ] }
         is={ ?b [ "b" <uvar> ] }
         ! { In ?s 0 ?a } { In ?s 1 ?b }
         ! { Out ?t 0 ?b } { Out ?t 1 ?a }
         { State ?s 0 ?a } { State ?t 1 ?a }
         { State ?s 1 ?b } { State ?t 0 ?b }
       }
    ! CHR{ // { Word drop ?s ?t } -- | { Shift ?s ?t 0 } }
    ! CHR{ { Shift ?s ?t ?d } // { In ?t ?m }  }
    ! Pop is defined between states
    CHR{ // { Word ?s ?t drop } -- |
         is={ ?a [ "X" <uvar> ] }
         { Pop ?s ?t ?a }
       }
    CHR{ // { Word ?s ?t dup } -- |
         is={ ?a [ "a" <uvar> ] }
         { State ?s 0 ?a } { Push ?s ?t ?a }
         ! { State ?s 0 ?a } { State ?s 1 ?a }
         ! { ShiftPush ?s ?t 1 }
       }
    CHR{ // { Pop ?s ?t ?a } -- |
         ! { Out ?s 0 ?a }
         { State ?s 0 ?a }
         { ShiftPop ?s ?t 1 } }
    CHR{ // { Push ?s ?t ?b } -- |
         ! { In ?t 0 ?b }
         { State ?t 0 ?b }
         { ShiftPush ?s ?t 1 }
       }
    CHR{ // { Word ?s ?t + } -- |
       is={ ?s1 [ "sp_plus" uvar ] }
       is={ ?s2 [ "sp_plus" uvar ] }
       is={ ?a [ "a" <uvar> ] }
       is={ ?b [ "b" <uvar> ] }
       is={ ?c [ "c" <uvar> ] }
         { Pop ?s ?s1 ?a }
         { Pop ?s1 ?s2 ?b }
         { Call ?s ?t + { ?a ?b } { ?c } }
         { Push ?s2 ?t ?c }
         { Def ?t ?c 0 }
       }
    ! CHR{ // { ShiftPush ?s ?t ?d } { ShiftPop ?t ?u ?d } -- | }
    ! CHR{ // { ShiftPop ?s ?t ?d } { ShiftPush ?t ?u ?d } -- | }
    CHR{ // { ShiftPop ?s ?t ?d } { ShiftPop ?t ?u ?e } -- |
       is={ ?l [ ?d ?e + ] }
         { ShiftPop ?s ?u ?l }
       }
    CHR{ // { ShiftPush ?s ?t ?d } { ShiftPush ?t ?u ?e } -- |
       is={ ?l [ ?d ?e + ] }
         { ShiftPop ?s ?u ?l }
       }
    ! ! Request from left
    CHR{ { ShiftPop ?s ?t ?d } { State ?s ?n ?a } // -- [ ?n ?d >= ] |
         is={ ?l [ ?n ?d - ] }
         { State ?t ?l ?a }
       }
    ! ! Request from right
    CHR{ { ShiftPop ?s ?t ?d } { State ?t ?n ?a } // -- |
         is={ ?l [ ?n ?d + ] }
         { State ?s ?l ?a }
       }
    ! ! Request from left
    CHR{ { ShiftPush ?s ?t ?d } { State ?s ?n ?a } // -- |
         is={ ?l [ ?n ?d + ] }
         { State ?t ?l ?a }
       }
    ! ! Request from right
    CHR{ { ShiftPop ?s ?t ?d } { State ?t ?n ?a } // -- [ ?n ?d >= ] |
         { State ?s ?l ?a }
         is={ ?l [ ?n ?d - ] }
       }
    ! ! Request from left
    ! CHR{ { ShiftPop ?s ?t ?d } { In ?s ?m ?a } // -- [ ?m ?d >= ] |
    !      { Out ?s ?m ?a }
    !      { In ?t ?l ?a }
    !      is={ ?l [ ?m ?d - ] } }
    ! ! Request from Right
    ! CHR{ { ShiftPop ?s ?t ?d } { Out ?t ?m ?a } // -- |
    !      { In ?t ?m ?a }
    !      { Out ?s ?l ?a }
    !    is={ ?l [ ?m ?d + ] } }
    ! ! Request from left
    ! CHR{ { ShiftPush ?s ?t ?d } { In ?s ?m ?a } // -- |
    !      { Out ?s ?m ?a }
    !      { In ?t ?l ?a }
    !    is={ ?l [ ?m ?d + ] } }
    ! ! Request from Right
    ! CHR{ { ShiftPush ?s ?t ?d } { Out ?t ?m ?a } // -- [ ?m ?d >= ] |
    !      { In ?t ?m ?a }
    !      { Out ?s ?l ?a }
    !    is={ ?l [ ?m ?d - ] } }
    CHR{ // { Infer1 ?s ?t ?a } -- [ W{ ?a } word? ] | { Word ?s ?t ?a } }
    CHR{ // { Infer ?s [ ] } -- | { Return ?s } }
    CHR{ // { Infer ?s ?q } -- |
         is={ ?a [ ?q first ] }
         is={ ?b [ ?q rest ] }
         is={ ?t [ ?s make-next-state ] }
         { Infer1 ?s ?t ?a }
         { Infer ?t ?b }
       }
    CHR{ // { StartInfer ?s ?q } -- | { Infer ?s ?q } { Start ?s } }
    CHR{ { Return ?s } // { State ?s ?n ?x } -- | { Retval ?s ?n ?x } }
    CHR{ { Start ?s } // { State ?s ?n ?x } -- | { Param ?s ?n ?x } }
    ! CHR{ { Stack ?s ?a } { Stack ?t ?b } // -- ={ ?a ?b } | { Conn ?a ?b } }
    ! CHR{ { // Conn L{ ?a . ?r } L{ ?b . ?s } } }
    ! CHR{ { Out ?t ?l } // -- | { Defs ?t ?l } }
    ! CHR{ // { Defs ?t ?r } -- [ ?r nil? ] | }
    ! CHR{ // { Defs ?t { ?a . ?r } } -- | { Defs ?t ?r } { Def ?t ?a } }
    ! CHR{ //  }
}
