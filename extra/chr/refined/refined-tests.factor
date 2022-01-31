USING: chr chr.refined kernel match math sequences sorting tools.test types.util
words ;
IN: chr.refined.tests

MATCH-VARS: ?x ?y ?z ;
SYMBOLS: A B C ;
SINGLETON: leq

! Original syntax:
!    rule-name @ H_keep \ H_remove => G | B
! Our syntax (named/anonymous):
!    CHR: rule-name @ H_keep // H_remove -- G | B ;
!    CHR{ H_keep // H_remove -- G | B }

CONSTANT: leq-ex {
    CHR: reflexivity @ // { leq ?x ?y } -- ={ ?x ?y } | ;
    CHR: antisymmetry @ // { leq ?x ?y } { leq ?y ?x } -- | ={ ?x ?y } ;
    CHR: transitivity @ { leq ?x ?y } { leq ?y ?z } // -- | { leq ?x ?z } ;
    ! CHR: idempotency @ { leq ?x ?y } // { leq ?x ?y } -- | ;
}

{ { }
  { ={ A B } ={ C B } } }
[ leq-ex { { leq A B } { leq B C } { leq C A } } chr-run-refined ] unit-test

MATCH-VARS: ?i ?j ?k ;
SINGLETON: gcd
CONSTANT: gcd-prog {
    CHR{ // { gcd 0 } -- | }
    CHR{ { gcd ?i } // { gcd ?j } -- [ ?j ?i >= ] |
         gen{ ?k |
             is={ ?k [ ?j ?i - ] }
             { gcd ?k }
          }
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
: make-next-state ( sname -- sname )
    drop "s" uvar ;

! ShiftPop/Push is a parallel constraint, which connects all undefined in/outs below a certain level
! Transitions are atomic and well ordered
! Shift{ prev next cut_in shift-by }
CONSTANT: stack-ex {
    ! Connection
    ! Keep single source
    CHR{ { State ?s ?n ?a } // { State ?s ?n ?b } -- | ={ ?b ?a } }
    CHR{ // { Word ?s ?t swap } -- |
         gen{ ?a ?b |
             { State ?s 0 ?a } { State ?t 1 ?a }
             { State ?s 1 ?b } { State ?t 0 ?b }
          }
       }
    ! Pop is defined between states
    CHR{ // { Word ?s ?t drop } -- |
         gen{ "X" |
             { Pop ?s ?t "X" }
          }
       }
    CHR{ // { Word ?s ?t dup } -- |
         gen{ ?a |
             { State ?s 0 ?a } { Push ?s ?t ?a }
          }
       }
    CHR{ // { Pop ?s ?t ?a } -- |
         { State ?s 0 ?a }
         { ShiftPop ?s ?t 1 } }
    CHR{ // { Push ?s ?t ?b } -- |
         { State ?t 0 ?b }
         { ShiftPush ?s ?t 1 }
       }
    CHR{ // { Word ?s ?t + } -- |
       is={ ?s1 [ "sp_plus" uvar ] }
       is={ ?s2 [ "sp_plus" uvar ] }
       gen{ ?a ?b ?c |
           { Pop ?s ?s1 ?a }
           { Pop ?s1 ?s2 ?b }
           { Call ?s ?t + { ?a ?b } { ?c } }
           { Push ?s2 ?t ?c }
           { Def ?t ?c 0 }
        }
       }
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
         is={ ?l [ ?n ?d - ] }
         { State ?s ?l ?a }
       }
    CHR{ // { Infer1 ?s ?t ?a } -- [ W{ ?a } word? ] | { Word ?s ?t ?a } }
    CHR{ // { Infer ?s [ ] } -- | { Return ?s } }
    CHR{ // { Infer ?s ?q } -- |
         is={ ?a [ ?q first ] }
         is={ ?b [ ?q rest ] }
         is={ ?t [ ?s make-next-state ] }
         { Infer1 ?s ?t ?a }
         { Infer ?t ?b }
       }
    CHR{ // { StartInfer ?s ?q } -- | { Start ?s } { Infer ?s ?q } }
    CHR{ { Return ?s } // { State ?s ?n ?x } -- | { Retval ?s ?n ?x } }
    CHR{ { Start ?s } // { State ?s ?n ?x } -- | { Param ?s ?n ?x } }
    ! Gobble up any remaining intermediate states
    CHR{ { Return ?s } // { State ?t ?n ?x } -- | }
}

{ { { Param "s0" 0 T{ gvar f "?a1" } }
    { Param "s0" 1 T{ gvar f  "?b1"  } }
    { Return "s1" }
    { Retval "s1" 0 T{ gvar f  "?b1"  } }
    { Retval "s1" 1 T{ gvar f "?a1" } }
    { Start "s0" } } }
[ stack-ex { { StartInfer "s0" [ swap ] } } chr-run-refined drop natural-sort ] unit-test

{ { { Param "s0" 0 T{ gvar f "?a1" } }
    { Param "s0" 1 T{ gvar f  "?b1"  } }
    { Return "s2" }
    { Retval "s2" 0 T{ gvar f  "?a1"  } }
    { Retval "s2" 1 T{ gvar f "?b1" } }
    { Start "s0" } } }
[ stack-ex { { StartInfer "s0" [ swap swap ] } } chr-run-refined drop natural-sort ] unit-test
