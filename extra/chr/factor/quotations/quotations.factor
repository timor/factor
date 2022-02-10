USING: accessors arrays chr chr.factor chr.factor.words chr.parser chr.state
effects generic kernel math math.parser quotations sequences sets types.util
words ;

IN: chr.factor.quotations
FROM: syntax => _ ;

! * Quotation Inference
TERM-VARS: ?e ?i ?l ?o ?p ?q ?r ?s ?t ?u ?a ?b ?c ?d ?n ?m ?v ?w ?x ?xs ?y ?z ;

! ! ** Keep track of word sequencing
! TUPLE: word-link < chr-pred a b c ;
! ! TUPLE: link-seq < chr-pred pred succ o ;

! CHRAT: call-seq { link-seq }
! ! CHR{ { Word ?s ?t __ } // -- | { word-link ?s ?t } }
! CHR{ { word-link ?s ?t ?u } // { word-link ?s ?t ?u } -- | }
! ! CHR{ { word-link ?s ?t ?t } // { word-link ?s ?t ?u } -- | { word-link ?s ?u ?u } }
! ! CHR{ { word-link ?s ?s ?t } // { word-link ?s ?s ?u } -- | { word-link ?s ?u ?u } }
! ! CHR{ // { ask { link-seq ?s ?s ?s } } -- | { entailed { link-seq ?s ?s ?s } } }
! CHR{ { word-link ?s ?t ?t } // { ask { link-seq ?s ?t ?t } } -- | { entailed { link-seq ?s ?t ?t } } }
! CHR{ { Word ?r ?s } { Word ?s ?t } // { word-link ?s ?t ?t } -- | { word-link ?r ?s ?s } }
!     ;

! ** Low-level Stack operations


! { ShiftStack n_in n_out }
! Specifies opaque stack operation on top of the stack
! --/ 1     \ ------  1
! ...          ...
! ---/ n_in     \--- n_out
! --------- ... ----
! TUPLE: Pop < trans-pred val ;
TUPLE: Pops < state-pred vals ;
TUPLE: Pushes < state-pred vals ;

TUPLE: ShiftPush < trans-pred d ;
TUPLE: ShiftPop < trans-pred d ;

TUPLE: ShiftStack < trans-pred n-in n-out ;
TUPLE: Swap < trans-pred ;

: elt-vars ( seq -- seq )
    [ swap dup pair? [ first ] when
      [ nip ] [ number>string "v" prepend ] if*
      uvar
      <term-var>
    ] map-index ;

CHRAT: stack-ops { Pops Pushes }
CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?a } -- | }
CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?b } -- | [ ?b ?a ==! ] }

! Sanity check
CHR{ { Val __ ?n __ } // -- [ ?n 0 < ] | [ "error" throw ] }

! CHR{ // { Pops ?s ?a } -- [ ?a empty? ] | }
! CHR{ // { Pushes ?s ?a } -- [ ?a empty? ] | }

! CHR{ // { Pops ?s ?t ?a } -- | [ ?a [ f ] [| seq | seq unclip :> ( rest e ) ?s sub-state :> s1 { { Pops s1 ?t rest } { Pop ?s s1 e } } ] if-empty ] }
! CHR{ // { Pops ?s ?t ?a } -- | [ ?a [ f ] [| seq | seq unclip :> ( rest e ) ?s sub-state :> s1 { { Pops s1 ?t rest } { Pop ?s s1 e } } ] if-empty ] }
! CHR{ // { Pop ?s ?t { ?a ?u } } -- | { Pop ?s ?t ?a } { Instance ?a ?u } }
! CHR{ // { Pop ?s ?t ?a } -- |
!      { Val ?s 0 ?a }
!      { ShiftPop ?s ?t 1 } }

CHR{ { AssumeEffect ?s ?t ?e } // -- |
     [| | ?e [ in>> ] [ out>> ] bi 2dup :> ( i o )
      [ length ] bi@ :> ( ni no )
      f
      ?e bivariable-effect? [ { ShiftStack ?s ?t ni no } suffix ] unless
      i [ elt-vars ?s swap Pops boa suffix ] unless-empty
      o [ elt-vars ?t swap Pushes boa suffix ] unless-empty
     ] }

! CHR{ // { Pushes ?s ?t ?a } -- | [ ?a [ f ] [| seq | seq unclip :> ( rest e ) ?s sub-state :> s1 { { Pushes s1 ?t rest } { Push ?s s1 e } } ] if-empty ] }
! CHR{ // { Push ?s ?t { ?a ?u } } -- | { Push ?s ?t ?a } { Instance ?a ?u } }
CHR{ { Push ?s ?t ?b } // -- |
     { Val ?t 0 ?b }
     ! { ShiftPush ?s ?t 1 }
     { ShiftStack ?s ?t 0 1 }
     { Pushes ?t { ?b } }
   }

! Request from left
CHR: shiftstack-left @ { ShiftStack ?s ?t ?i ?o } { Val ?s ?n ?a } // -- [ ?n ?i > ]
     | [| | ?n ?o ?i - + :> m { Val ?t m ?a } ] ;
! Request from Right
CHR: shiftstack-right @ { ShiftStack ?t ?u ?i ?o } { Val ?u ?n ?a } // -- [ ?n ?o > ]
     | [| | ?n ?o ?i - - :> m { Val ?t m ?a } ] ;


! Transitivity
CHR: shiftstack-trans @
// { ShiftStack ?s ?t ?a ?b } { ShiftStack ?t ?u ?c ?d } -- |
[| |
 ?a ?c ?b [-] + :> i1
 ?b ?c [-] ?d + :> o2
 { ShiftStack ?s ?u i1 o2 }
] ;

! CHR{ // { ShiftPop ?s ?t ?d } { ShiftPop ?t ?u ?e } -- |
!      [| | ?d ?e + :> l { ShiftPop ?s ?u l } ]
!    }
! CHR{ // { ShiftPush ?s ?t ?d } { ShiftPush ?t ?u ?e } -- |
!      [| | ?d ?e + :> l { ShiftPush ?s ?u l } ]
!    }

    ;
! ** Effects
! This handles constraints that use stack effect defs to establish facts about
! program states
! TUPLE: Stack < trans-pred list ;
! TUPLE: Stack < trans-pred list ;
! TUPLE: DeclaredEffect < chr-pred val effect ;
! CHRAT: effect-constraints { }
!     CHR{ // { Effect ?s ?u ?x } -- | }
!     CHR{ // { Stack ?s ?t +nil+ } -- | }
!     CHR{ // { Stack ?s ?t L{ { ?v ?u } } } --
!          | [| | ?l uncons :> ( next rest ) { { Stack ?s ?t ?rest } Pops {  } } ]
!     }

! ;

! ** Def-Use
TUPLE: Def < state-pred n val ;
TUPLE: Use < state-pred n val ;
TUPLE: Unused < chr-pred val ;

CHRAT: def/use { }
    ;

TERM-VARS: ?beg ;

TUPLE: ExecUnknown < Exec ;
TUPLE: InlineQuot < trans-pred quot ;
TUPLE: EndQuot < trans-pred ;
TUPLE: Infer < chr-pred beg s quot ;
TUPLE: InferToplevelQuot < chr-pred quot ;
TUPLE: InferDef < chr-pred word ;
TUPLE: Linkback < chr-pred beg states ;
TUPLE: Entry < state-pred word ;

! ** Call-Graph-Inference
TUPLE: CheckExec < trans-pred word ;
TUPLE: RecursiveCall < trans-pred word back-to ;
! TUPLE: NonrecursiveCall < trans-pred word ;
TUPLE: Calls < chr-pred from caller to callee ;
! TUPLE: Top < state-pred ;
TUPLE: Link < chr-pred from to ;
! TUPLE: link-seq < chr-pred word pred succ o ;
CHRAT: call-stack { CheckExec }
CHR{ { Link ?t ?u } // { Link ?t ?u } -- | }
CHR{ { Entry ?r ?w } // { Link ?r ?s } { CheckExec ?s ?t ?w } --
     | { RecursiveCall ?s ?t ?w ?r } }
CHR{ // { Link +top+ ?s } { CheckExec ?s ?t ?w } --
     | { ExecWord ?s ?t ?w } }
CHR{ { CheckExec ?t __ ?w } { Linkback ?s ?l } // -- [ ?t ?l in? ] |
     { Link ?s ?t } }
CHR{ { Linkback ?s ?l } // { Link ?t ?u } -- [ ?t ?l in? ] | { Link ?s ?u } }
    ;

! ** Word-level Inference
TUPLE: Stack < state-pred n vars ;
TUPLE: Prim < Word ;
CHRAT: infer-stack { Word }
IMPORT: stack-ops
IMPORT: def/use
! CHR{ { InferUnknown __ __ ?q } // -- | { Instance ?q callable } }
! CHR{ { BranchIf __ __ ?c __ __ } // -- | { Instance ?c boolean } }
CHR{ // { Word ?s ?t dup } --
     | { Prim ?s ?t dup }
     { Val ?s 0 ?a } { Val ?t 0 ?b } { Val ?t 1 ?a } { Split ?a ?b }
     { ShiftStack ?s ?t 1 2 }
   }
CHR{ // { Word ?s ?t drop } -- |
     { Prim ?s ?t dup }
     { ShiftStack ?s ?t 1 0 } { Val ?s 0 ?x } { Unused ?x }
   }
CHR{ // { Word ?s ?t swap } -- |
     { Prim ?s ?t dup }
     { ShiftStack ?s ?t 2 2 } { Val ?s 0 ?a } { Val ?s 1 ?b }
     { Val ?t 0 ?b } { Val ?t 1 ?a }
   }
CHR{ // { Word ?s ?t ?w } -- [ ?w generic? ] | { Generic ?s ?t ?w } }
CHR{ { Word ?s ?t ?w } // -- |
     [| | ?w stack-effect :> e { AssumeEffect ?s ?t e } ] }
! CHR{ { Word ?s ?t ?w } // -- [ W{ \ ?w } \ tell-chr* ?lookup-method ] | [ ?s ?t ?w tell-chr ] }
! CHR{ // { Word ?s ?t ?w } -- [ ?w inline? ] | { InlineCall ?s ?t ?w } }

! Inferred stack elements
CHR{ { EndQuot ?s ?t } { ShiftStack ?s ?t ?i ?o } // -- |
     [| | ?i 1 - :> ni ?o 1 - :> no
      { { Stack ?s ni { } }
        { Stack ?t no { } } } ] }

CHR{ { Val ?s ?n ?a } // { Stack ?s ?n ?l } -- [ ?n 0 >= ] |
     [| | ?n 1 - :> m ?l ?a suffix :> a2 { Stack ?s m a2 } ]
   }

CHR{ // { Stack ?s -1 ?i } { Stack ?t -1 ?o } -- | [| |
         ! ?i ?o [ [ name>> ] map ] bi@ <effect> :> e
         { InferredEffect ?s ?t { ?i ?o } }
                                              ] }
CHR{ { Stack ?s ?n __ } // -- [ ?n 0 >= ] | { Val ?s ?n ?x } }
    ;


! ** Syntactic expansion
TUPLE: BeginQuot < trans-pred ;
CHRAT: expand-quot { InferDef InferToplevelQuot }
IMPORT: call-stack
IMPORT: infer-stack
IMPORT: stack-ops
CHR{ // { InferDef ?w } -- [ ?w deferred? not ] |
     [| | state-in state-out :> ( si so )
      ?w def>> :> def
      ?w :> w
      {
          { Entry +top+ w }
          { InlineQuot +top+ +end+ def }
      }
     ] }

CHR{ { InlineQuot ?s ?t ?q } // -- | [| |
                                  ! ?s sub-state :> si
                                  ?s seq-state :> si
                                  { { Linkback ?s { si }
                                    } { BeginQuot ?s si } { Infer si si ?q } } ] }
! CHR{ { InlineQuot ?s ?t ?q } // -- | [| |
!                                      ?s sub-state :> si
!                                      { { Linkback ?s { si } } { Infer si se ?q } } ] }
CHR{ // { InferToplevelQuot ?q } -- | [ +top+ +end+ ?q InlineQuot boa ] }
CHR{ { BeginQuot ?r ?beg } // { Infer ?beg ?s [ ] } -- | { EndQuot ?beg ?s } }
CHR{ { BeginQuot ?r ?beg } // { Linkback ?r ?a } { Infer ?beg ?s ?q } -- |
     [| | ?q unclip :> ( rest w ) ?s seq-state :> sn
      ?a sn suffix :> a2
      { { Exec ?s sn w } { Infer ?beg sn rest } { Linkback ?r a2 } } ] }
! CHR{ // { Exec ?s ?t ?w } -- [ ?w word? ]
!      | [ ?w deferred? { ExecUnknown ?s ?t ?w } { CheckExec ?s ?t ?w } ? ] }
CHR{ // { Exec ?s ?t ?w } -- [ ?w word? ] | { CheckExec ?s ?t ?w } }
CHR{ // { Exec ?s ?t ?w } -- [ ?w known? ] | { Push ?s ?t ?w } }
CHR{ // { ExecWord ?s ?t ?w } -- [ ?w inline? ]
     | [| | ?w def>> :> def { InlineCall ?s ?t ?w def } ] }
CHR{ // { InlineCall ?s ?t ?w ?d } -- | { Entry ?s ?w } { InlineQuot ?s ?t ?d } }
CHR{ // { ExecWord ?s ?t ?w } -- | { Word ?s ?t ?w } }
;

! * Interface
! : chrat-infer ( quot -- constraints )
!     '{ { InferToplevelQuot _ } } run-chrat-query ;

:: chrat-infer-with ( prog w -- constraints )
    prog
    w word?
    ! [ expand-quot swap '{ { InferDef _ } } run-chr-query ]
    [ { { InferDef w } } run-chr-query ]
    [ { { InferToplevelQuot w } } run-chr-query ] if ;

: chrat-infer ( quot/word -- constraints )
    dup word?
    ! [ expand-quot swap '{ { InferDef _ } } run-chr-query ]
    [ '{ { InferDef _ } } run-chrat-query ]
    [ '{ { InferToplevelQuot _ } } run-chrat-query ] if ;
