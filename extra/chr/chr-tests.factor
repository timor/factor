USING: accessors assocs chr chr.parser chr.programs chr.state kernel
linked-assocs math sequences tools.test types.util words ;
IN: chr.tests


TUPLE: gcd < chr-pred val ;
C: <gcd> gcd

TERM-VARS: ?i ?j ;

! TODO Test with symbolic leq
CONSTANT: gcd-ex {
CHR: gcd1 @ // { gcd ?i } -- [ ?i 0 == ] | ;
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


! Passing Stuff via stack?
SYMBOLS: Stack State Word Before After Conn In Out Defs Def Comp Push Pop ShiftPop
    ShiftPush Unshift Prim Call Use ;
SYMBOLS: StartInfer EndInfer Start Infer Infer1 Return Retval Param ;
TERM-VARS: ?a ?b ?c ?r ?s ?s1 ?s2 ?s3 ?t ?u ?v ?w ?n ?m ?l ?d ?e ?q ;

: make-next-state ( sname -- sname )
    drop "s" uvar ;

! ShiftPop/Push is a parallel constraint, which connects all undefined in/outs below a certain level
! Transitions are atomic and well ordered
! Shift{ prev next cut_in shift-by }
CONSTANT: stack-ex {
    ! Connection
    ! Dedup in case we infer equivalent states
    CHR{ { State ?s ?n ?a } // { State ?s ?n ?a } -- | }
    ! Keep single source
    CHR{ { State ?s ?n ?a } // { State ?s ?n ?b } -- | [ ?b ?a ==! ] }
    ! CHR{ { State ?s ?n ?a } { State ?s ?n ?b } // -- | [ ?b ?a ==! ] }
    CHR{ // { Word ?s ?t swap } -- |
         { State ?s 0 ?a } { State ?t 1 ?a }
         { State ?s 1 ?b } { State ?t 0 ?b }
       }
    ! Pop is defined between states
    CHR{ // { Word ?s ?t drop } -- |
         { Pop ?s ?t ?x }
       }
    CHR{ // { Word ?s ?t dup } -- |
         { State ?s 0 ?a } { Push ?s ?t ?a }
       }
    CHR{ // { Pop ?s ?t ?a } -- |
         { State ?s 0 ?a }
         { ShiftPop ?s ?t 1 } }
    CHR{ // { Push ?s ?t ?b } -- |
         { State ?t 0 ?b }
         { ShiftPush ?s ?t 1 }
       }
    CHR{ // { Word ?s ?t + } -- |
         [| |
          "sp_plus" uvar :> s1
          "sp_plus" uvar :> s2
          {
              { Pop ?s s1 ?a }
              { Pop s1 s2 ?b }
              { Call ?s ?t + { ?a ?b } { ?c } }
              { Push s2 ?t ?c }
              { Def ?t ?c 0 }
          } ]
       }
    ! Transitivity
    ! NOTE: does not work since e.g. dup dup will then forget about the middle
    ! output element
    ! CHR{ // { ShiftPop ?s ?t ?d } { ShiftPop ?t ?u ?e } -- |
    !      [| | ?d ?e + :> l { ShiftPop ?s ?u l } ]
    !    }
    ! CHR{ // { ShiftPush ?s ?t ?d } { ShiftPush ?t ?u ?e } -- |
    !      [| | ?d ?e + :> l { ShiftPush ?s ?u l } ]
    !    }
    ! Sanity check
    CHR{ { State __ ?n __ } // -- [ ?n 0 < ] | [ "error" throw ] }
    ! ShiftPop
    ! ---↗  /------
    ! -----/ ↗-----
    ! ! Request from left
    CHR{ { ShiftPop ?s ?t ?d } { State ?s ?n ?a } // -- [ ?n ?d >= ] |
         [| | ?n ?d - :> l
          { State ?t l ?a }
         ]
       }
    ! ! Request from right
    CHR{ { ShiftPop ?s ?t ?d } { State ?t ?n ?a } // -- |
         [| | ?n ?d + :> l
          { State ?s l ?a }
         ]
       }
    ! ShiftPush
    ! ----\  ↘------
    ! ---↘ \--------
    ! ! Request from left
    CHR{ { ShiftPush ?s ?t ?d } { State ?s ?n ?a } // -- |
         [| | ?n ?d + :> l { State ?t l ?a } ]
       }
    ! ! Request from right
    CHR{ { ShiftPush ?s ?t ?d } { State ?t ?n ?a } // -- [ ?n ?d >= ] |
         [| | ?n ?d - :> l { State ?s l ?a } ]
       }
    ! CHR{ // { Infer1 ?s ?t ?a } -- [ W{ ?a } word? ] | { Word ?s ?t ?a } }
    CHR{ // { Infer1 ?s ?t ?a } -- [ ?a word? ] | { Word ?s ?t ?a } }
    CHR{ // { Infer ?s [ ] } -- | { Return ?s } }
    CHR{ // { Infer ?s ?q } -- |
         [| | ?q first :> a
           ?q rest :> b
           ?s make-next-state :> snext
           {
               { Infer1 ?s snext a }
               { Infer snext b }
           }
         ]
       }
    CHR{ // { StartInfer ?s ?q } -- | { Start ?s } { Infer ?s ?q } }
    CHR{ { Return ?s } { State ?s ?n ?x } // -- | { Retval ?s ?n ?x } }
    CHR{ { Start ?s } { State ?s ?n ?x } // -- | { Param ?s ?n ?x } }
    ! Gobble up any remaining intermediate states
    CHR{ { Return ?s } // { State ?t ?n ?x } -- | }
}

{ LH{
      { 2 { Start "s0" } }
      { 7 { Param "s0" 0 G{ ?a1 } } }
      { 10 { Param "s0" 1 G{ ?b1 } } }
      { 13 { Return "s1" } }
      { 14 { Retval "s1" 1 G{ ?a1 } } }
      { 15 { Retval "s1" 0 G{ ?b1 } } }
} }
[ stack-ex { { StartInfer "s0" [ swap ] } } run-chr-query ] unit-test

{ LH{
      { 2 { Start "s0" } }
      { 7 { Param "s0" 0 G{ ?b2 } } }
      { 10 { Param "s0" 1 G{ ?a2 } } }
      { 16 { = G{ ?a2 } G{ ?b1 } } }
      { 19 { = G{ ?b2 } G{ ?a1 } } }
      { 22 { Return "s2" } }
      { 23 { Retval "s2" 1 G{ ?a2 } } }
      { 24 { Retval "s2" 0 G{ ?b2 } } }
} }
[ stack-ex { { StartInfer "s0" [ swap swap ] } } run-chr-query ] unit-test

{ {
        { Start "s0" }
        { Param "s0" 0 G{ ?a1 } }
        { ShiftPop "s0" "sp_plus1" 1 }
        { Param "s0" 1 G{ ?b1 } }
        { ShiftPop "sp_plus1" "sp_plus2" 1 }
        { Call "s0" "s1" + { G{ ?a1 } G{ ?b1 } } { G{ ?c1 } } }
        { ShiftPush "sp_plus2" "s1" 1 }
        { Def "s1" G{ ?c1 } 0 }
        { Return "s1" }
        { Retval "s1" 0 G{ ?c1 } }
}
}
[ stack-ex { { StartInfer "s0" [ + ] } } run-chr-query values ] unit-test
