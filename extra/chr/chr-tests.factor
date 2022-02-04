USING: accessors chr chr.parser chr.state kernel linked-assocs math sequences
tools.test types.util words ;
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
    ! CHR{ // { ShiftPop ?s ?t ?d } { ShiftPop ?t ?u ?e } -- |
    !      ! { is ?l [ ?d ?e + ] }
    !      [| | ?d ?e + :> l { ShiftPop ?s ?u l } ]
    !    }
    ! CHR{ // { ShiftPush ?s ?t ?d } { ShiftPush ?t ?u ?e } -- |
    !      ! { is ?l [ ?d ?e + ] }
    !      [| | ?d ?e + :> l { ShiftPop ?s ?u l } ]
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
    CHR{ // { Infer1 ?s ?t ?a } -- [ W{ ?a } word? ] | { Word ?s ?t ?a } }
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
    CHR{ // { StartInfer ?s ?q } -- | { Infer ?s ?q } { Start ?s } }
    ! CHR{ { Return ?s } // { State ?s ?n ?x } -- | { Retval ?s ?n ?x } }
    CHR{ { Return ?s } { State ?s ?n ?x } // -- | { Retval ?s ?n ?x } }
    CHR{ { Start ?s } { State ?s ?n ?x } // -- | { Param ?s ?n ?x } }
    ! Gobble up any remaining intermediate states
    ! CHR{ { Return ?s } // { State ?t ?n ?x } -- | }
}

{ LH{
      { 10 { Return "s1" } }
      { 11 { Retval "s1" 1 G{ ?a1 } } }
      { 12 { Retval "s1" 0 G{ ?b1 } } }
      { 13 { Start "s0" } }
      { 14 { Param "s0" 0 G{ ?a1 } } }
      { 15 { Param "s0" 1 G{ ?b1 } } }
} }
[ stack-ex { { StartInfer "s0" [ swap ] } } run-chr-query ] unit-test

{ LH{
      { 6 { State "s1" 1 G{ ?b2 } } }
      { 8 { State "s1" 0 G{ ?a2 } } }
      { 13 { = G{ ?a2 } G{ ?b1 } } }
      { 16 { = G{ ?b2 } G{ ?a1 } } }
      { 19 { Return "s2" } }
      { 20 { Retval "s2" 1 G{ ?a2 } } }
      { 21 { Retval "s2" 0 G{ ?b2 } } }
      { 22 { Start "s0" } }
      { 23 { Param "s0" 0 G{ ?b2 } } }
      { 24 { Param "s0" 1 G{ ?a2 } } }
} }
[ stack-ex { { StartInfer "s0" [ swap swap ] } } run-chr-query ] unit-test
