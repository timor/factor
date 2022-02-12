USING: accessors arrays chr chr.factor chr.factor.words chr.modular chr.parser
chr.programs chr.state generic kernel math math.order math.parser sequences sets
types.util words ;

IN: chr.factor.quotations
FROM: syntax => _ ;

! * Quotation Inference
TERM-VARS: ?e ?i ?l ?o ?p ?q ?r ?s ?st ?sf ?t ?u ?a ?b ?c ?d ?n ?m ?v ?w ?x ?xs ?y ?z ?c1 ?c2 ;

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

! ** Low-level InferredStack operations


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

TUPLE: Shuffle < trans-pred mapping ;

: elt-vars ( seq -- seq )
    [ swap dup pair? [ first ] when
      [ nip ] [ number>string "v" prepend ] if*
      uvar
      <term-var>
    ] map-index <reversed> ;

CHRAT: stack-ops { }
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

! Request from left
CHR: shiftstack-left @ { ShiftStack ?s ?t ?i ?o } { Val ?s ?n ?a } // -- [ ?n ?i >= ]
     | [| | ?n ?o ?i - + :> m { Val ?t m ?a } ] ;
! Request from Right
CHR: shiftstack-right @ { ShiftStack ?t ?u ?i ?o } { Val ?u ?n ?a } // -- [ ?n ?o >= ]
     | [| | ?n ?o ?i - - :> m { Val ?t m ?a } ] ;


! Transitivity
! Known values have been transported, so we can delete any intermediates
! CHR: shiftstack-trans1 @
! { ShiftStack ?s ?t ?a ?b } { ShiftStack ?t ?u ?c ?d } // { Val ?t ?n __ } -- [ ?n known? ] [ ?a known? ] [ ?b known? ] [ ?c known? ] [ ?d known? ] | ;
! ! [| |
! !  ?a ?c ?b [-] + :> i1
! !  ?b ?c [-] ?d + :> o2
! !  { ShiftStack ?s ?u i1 o2 }
! ! ] ;

CHR: shiftstack-trans @
// { ShiftStack ?s ?t ?a ?b } { ShiftStack ?t ?u ?c ?d } -- [ ?a known? ] [ ?b known? ] [ ?c known? ] [ ?d known? ] |
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
! TUPLE: InferredStack < trans-pred list ;
! TUPLE: InferredStack < trans-pred list ;
! TUPLE: DeclaredEffect < chr-pred val effect ;
! CHRAT: effect-constraints { }
!     CHR{ // { Effect ?s ?u ?x } -- | }
!     CHR{ // { InferredStack ?s ?t +nil+ } -- | }
!     CHR{ // { InferredStack ?s ?t L{ { ?v ?u } } } --
!          | [| | ?l uncons :> ( next rest ) { { InferredStack ?s ?t ?rest } Pops {  } } ]
!     }

! ;

! ** Def-Use
TUPLE: Def < state-pred n val ;
TUPLE: Use < state-pred n val ;
TUPLE: Unused < chr-pred val ;

CHRAT: def/use { }
    ;

TERM-VARS: ?beg ?parm ;

TUPLE: Prim < Word ;
TUPLE: ExecUnknown < Exec ;
TUPLE: InlineUnknown < trans-pred val ;
TUPLE: InlineCond < trans-pred val cond ;
TUPLE: InlineQuot < trans-pred quot cond ;
TUPLE: Cond < chr-pred cond constraint ;
! TUPLE: InlineDip < InlineQuot quot saved ;
TUPLE: InlinedQuot < InlineQuot ;
TUPLE: BeginQuot < trans-pred ;
TUPLE: EndQuot < trans-pred ;
TUPLE: Infer < chr-pred beg s quot ;
TUPLE: InferToplevelQuot < chr-pred quot ;
TUPLE: InferDef < chr-pred word ;
TUPLE: InferDip < trans-pred kept quot ;
TUPLE: Linkback < chr-pred beg states ;
TUPLE: LinkStates < trans-pred ;
TUPLE: InsertState < trans-pred between ;
TUPLE: Entry < state-pred word ;
TUPLE: CallFrame < chr-pred caller-start callee-start callee-end caller-end ;
TUPLE: InferBetween < trans-pred entry-state quot ;
TUPLE: InferredBetween < trans-pred entry-state exit-state quot ;

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
! CHR{ { CheckExec ?t __ ?w } { Linkback ?s ?l } // -- [ ?t known ?l known in? ] |
CHR{ { CheckExec ?t __ ?w } { Linkback ?s ?l } // -- [ ?t ?l in? ] |
     { Link ?s ?t } }
! CHR{ { Linkback ?s ?l } // { Link ?t ?u } -- [ ?t known ?l known in? ] | { Link ?s ?u } }
CHR{ { Linkback ?s ?l } // { Link ?t ?u } -- [ ?t ?l in? ] | { Link ?s ?u } }
! CHR{ { SplitState ?s ?s1 __ } // { Link ?s1 ?u } -- | { Link ?s ?u } }
! CHR{ { SplitState ?s __ ?s2 } // { Link ?s2 ?u } -- | { Link ?s ?u } }
CHR{ { CondJump ?s ?u __ } // { Link ?r ?u } -- | { Link ?s ?u } }
    ;

! ** Cleaner
TUPLE: DeleteBetween < chr-pred from to ;
TUPLE: DeleteState < chr-pred state ;
CHRAT: clean-states { DeleteBetween }
CHR{ { Linkback __ ?a } { DeleteBetween ?s ?t } //
     -- [ ?s known ?a known in? ] [ ?t known ?a known in? ] |
     [| | ?s ?a index 1 + ?t ?a index ?a subseq [| si | { DeleteState si } ] map ]
   }
CHR{ { DeleteState ?s } // { Val ?s __ __ } -- | }
CHR{ { DeleteState ?s } // { Linkback ?s ?a } -- |
     [ ?a [| si | { DeleteState } ] map ] }
CHR{ { DeleteState ?s } // { Prim ?s __ } -- | }
CHR{ // { DeleteState __ } -- | }
;

TUPLE: InferStack < state-pred n i vars ;

! ** Word-level Inference
CHRAT: infer-stack { Word }
IMPORT: stack-ops
IMPORT: clean-states
IMPORT: def/use
! CHR{ { InferUnknown __ __ ?q } // -- | { Instance ?q callable } }
! CHR{ { BranchIf __ __ ?c __ __ } // -- | { Instance ?c boolean } }
CHR{ // { Word ?s ?t dup } --
     | { Prim ?s ?t dup }
     { Val ?s 0 ?a } { Val ?t 0 ?b } { Val ?t 1 ?a } { Split ?a ?b }
     { ShiftStack ?s ?t 1 2 }
   }
CHR{ // { Word ?s ?t drop } -- |
     { Prim ?s ?t drop }
     { ShiftStack ?s ?t 1 0 } { Val ?s 0 ?x } { Unused ?x }
   }
CHR{ // { Word ?s ?t swap } -- |
     { Prim ?s ?t swap }
     { ShiftStack ?s ?t 2 2 } { Val ?s 0 ?a } { Val ?s 1 ?b }
     { Val ?t 0 ?b } { Val ?t 1 ?a }
   }

CHR{ // { Word ?r ?u dip } -- |
     { Prim ?r ?u dip }
     { Val ?r 0 ?q }
     { Val ?r 1 ?a }
     ! { InferDip ?r ?u ?a ?q }
     { ShiftStack ?r ?s 2 0 }
     { InsertState ?r ?u ?s }
     ! { LinkStates ?r ?s }
     ! { InlineQuot ?s ?t ?q }
     { ShiftStack ?t ?u 0 1 }
     { Val ?u 0 ?a }
     { InsertState ?s ?u ?t }
     ! { LinkStates ?t ?u }
   }

! CHR{ { Word ?s ?t ?w } // -- [ W{ \ ?w } \ tell-chr* ?lookup-method ] | [ ?s ?t ?w tell-chr ] }
! CHR{ // { Word ?s ?t ?w } -- [ ?w inline? ] | { InlineCall ?s ?t ?w } }

! Inferred stack elements
CHR{ { InlineQuot ?r ?u __ } { ShiftStack ?r ?u ?i ?o } // -- |
          ! { InferredStack ?r ni { } }
          ! { InferredStack ?u no { } }
          { InferStack ?r ?i 0 { } }
          { InferStack ?u ?o 0 { } }
        ! { BoundedEffect ?s ?t }
}

CHR{ // { InferStack ?s ?n ?n ?a } -- | { InferredStack ?s ?n ?a } }

CHR{ { Val ?s ?i ?a } // { InferStack ?s ?n ?i ?l } -- [ ?i known number? ] | [| | ?l ?a prefix :> new ?i 1 + :> j { InferStack ?s ?n j new  } ] }

! CHR{ { Val ?s ?n ?a } // { InferredStack ?s ?n ?l } -- [ ?n 0 >= ] |
! CHR{ { Val ?s ?n ?a } { InferredStack ?s ?n ?l } // -- [ ?n 0 >= ] |
!      [| | ?n 1 - :> m ?l ?a suffix :> a2 { InferredStack ?s m a2 } ]
!    }

! CHR{ { CallFrame ?r ?s ?t ?u } // { ShiftStack ?s ?t ?i ?o } -- |
!      { ShiftStack ?r ?u ?i ?o } }

! ! Wrap up inlined calls
CHR{ { ShiftStack ?s ?t __ __ } { InferredEffect ?s ?t __ } // ! { Linkback ?r __ }
     { InlineQuot ?r ?u ?q } { CallFrame ?r ?s ?t ?u }
     -- |
     ! { DeleteBetween ?s ?t }
     ! { InlinedQuot ?r ?u ?q } [ ?s ?r ==! ] [ ?t ?u ==! ]
     { InlinedQuot ?r ?u ?q } ! [ ?s ?r ==! ] [ ?t ?u ==! ]
     ! { ShiftStack ?r ?s 0 0 }
     ! { ShiftStack ?t ?u 0 0 }
   }
! CHR{ { ShiftStack ?s ?t __ __ } //
!      { InlineQuot ?r ?u ?q } { CallFrame ?r ?s ?t ?u } { Linkback ?r __ }
!      -- | { InlinedQuot ?r ?u ?q } [ ?s ?r ==! ] [ ?t ?u ==! ]
!    }

! Link Call Frame Values
CHR{ { CallFrame ?r ?s ?t ?u } // -- |
     { ShiftStack ?r ?s 0 0 }
     { ShiftStack ?t ?u 0 0 }
   }

CHR{ { CallFrame ?r ?s __ __ } { Val ?r ?n ?a } // -- | { Val ?s ?n ?a } }
CHR{ { CallFrame ?r ?s __ __ } { Val ?s ?n ?a } // -- | { Val ?r ?n ?a } }

CHR{ { CallFrame __ __ ?r ?s } { Val ?r ?n ?a } // -- | { Val ?s ?n ?a } }
CHR{ { CallFrame __ __ ?r ?s } { Val ?s ?n ?a } // -- | { Val ?r ?n ?a } }


! CHR{ { InlineQuot ?r ?u __ __ } //
!      { InferredStack ?r ?n ?i } { InferredStack ?u ?m ?o } -- |
!      [| |
!       ! ?i ?o [ [ name>> ] map ] bi@ <effect> :> e
!       { InferredEffect ?r ?u ?i ?o }
!      ] }

CHR{ { InferredStack ?s ?n __ } // -- [ ?n 0 >= ] | { Val ?s ?n ?x } }
    ;

:: complete-shuffle? ( in out e -- ? )
    { [ e out [ length ] same? ]
      [ e supremum 1 + in length = ]
    } 0&& ;

TERM-VARS: ?rho ?sig ;

! ** Effect Assumptions
CHRAT: basic-stack { Val Lit InferredEffect }
CHR{ { Word ?s ?t ?w } // -- |
     [| | ?w chrat-effect :> e { AssumeEffect ?s ?t e } ] }
CHR{ { AssumeEffect ?s ?t ?e } // -- |
     [| | ?e [ in>> ] [ out>> ] bi 2dup :> ( i o )
      [ length ] bi@ :> ( ni no )
      f
      ! ?e bivariable-effect? [ { ShiftStack ?s ?t ni no } suffix ] unless
      i elt-vars :> i
      o elt-vars :> o
      i [ ?s swap Pops boa suffix ] unless-empty
      o [ ?t swap Pushes boa suffix ] unless-empty

      ?s ?t
      i >list ?rho lappend
      {
          { [ ?e terminated?>> ] [ __ ] }
          { [ ?e bivariable-effect? ] [ o >list ?sig lappend ] }
          [ o >list ?rho lappend ] } cond InferredEffect boa suffix
     ] }

! CHR{ { AssumeEffect ?s ?t ?e } { Pops ?s ?i } { Pushes ?t ?o } // -- |
!      ! gen{ ?rho |
!           [| |
!          ?i >list ?rho lappend :> in
!          ?o >list ?rho lappend :> out
!          { InferredEffect ?s ?t in out }
!           ]
!         ! }
!    }

! CHR{ { InferredEffect ?s ?t ?a ?b } // { InferredEffect ?s ?t ?c ?d } -- |
!      [ { ?a ?b } { ?c ?d } unify
!        [ [ ?s ?t ] 2dip EitherOr boa ] { } assoc>map
!      ] }

! CHR{ { InferredEffect ?s ?t ?a ?b } { InlineQuot ?r ?u __ ?c } { InferredBetween ?r ?u ?s ?t __ } // -- [ ?c true == ] |
!      { InferredEffect ?r ?u ?a ?b }
!    }

CHR{ { InlineQuot ?r ?u __ ?c } { InferredBetween ?r ?u ?s ?t __ } // { InferredEffect ?s ?t ?a ?b } -- [ ?c true == ] |
     { InferredEffect ?r ?u ?a ?b }
   }

CHR{ // { InferredEffect ?r ?s ?a ?b } { InferredEffect ?s ?t ?b ?c } -- |
     { InferredEffect ?r ?t ?a ?c } }

CHR{ { InferredEffect ?r ?s ?a ?b } { InferredEffect ?s ?t ?c ?d } // -- |
     [ ?b ?c ==! ] }

! CHR{ { Pushes ?s ?l } // { ask { Val ?s ?n ?a } } -- [ ?n ?l length < ] | [ ?a ?n ?l nth ==! ] { entailed { Val ?s ?n ?a } } }
CHR{ { Pushes ?s ?l } { Val ?s ?n ?a } // -- [ ?n ?l length < ] | [ ?a ?n ?l nth ==! ] }
CHR{ { Pops ?s ?l } { Val ?s ?n ?a } // -- [ ?n ?l length < ] | [ ?a ?n ?l nth ==! ] }

! CHR{ // { Pushes ?s ?t ?a } -- | [ ?a [ f ] [| seq | seq unclip :> ( rest e ) ?s sub-state :> s1 { { Pushes s1 ?t rest } { Push ?s s1 e } } ] if-empty ] }
! CHR{ // { Push ?s ?t { ?a ?u } } -- | { Push ?s ?t ?a } { Instance ?a ?u } }
CHR{ { Push ?s ?t ?b } // -- |
     ! { Val ?t 0 ?b }
     ! { ShiftPush ?s ?t 1 }
     ! { ShiftStack ?s ?t 0 1 }
     { Pushes ?t { ?a } }
     { Val ?t 0 ?a }
     { Lit ?a ?b }
     { InferredEffect ?s ?t ?rho L{ ?a . ?rho } }
   }

CHR{ { Lit ?a ?b } // -- |
     [ ?a ?b class-of Instance boa ] }

! CHR{ { Pushes ?s ?t } }

! Two things in parallel: 1. Infer the quotation, 2. Transport the value
! CHR{ { Word ?s ?u dip } // -- { Val ?s 0 ?q }  |
!      { InlineQuot ?s ?t ?q }
!    }

! CHR{ { Word ?s ?u dip } // -- { Val ?s 1 ?a } |
!      { InlineQuot ?s ?t ?q } { Push ?t ?u ?a }
!    }
! FIXME: Have to make sure InlineQuot comes first because of replacement foo not working correctly right now
! Ideal fix: queue-based runner, so that we always see all var instances!
! CHR{ { Word ?s ?t dip  } // -- | { Val ?s 1 ?a } { Val ?s 0 ?q } { InlineQuot ?s ?t ?q } { Val ?t 0 ?a } }
CHR{ { Word ?s ?t dip } // -- | { InlineUnknown ?s ?t ?q } { Val ?s 1 ?a } { Val ?s 0 ?q } { Val ?t 0 ?a } }

CHR{ { Word ?s ?t call } // -- |
     { InferCall ?s ?t ?q } { Val ?s 0 ?q } }

CHR{ // { Word ?s ?t ?w } -- [ ?w "shuffle" word-prop? ] |
     [ ?s ?t ?w "shuffle" word-prop shuffle-mapping Shuffle boa ]
   }

CHR{ { Pops ?s ?i } { Pushes ?t ?o } // { Shuffle ?s ?t ?e }  -- [ ?i ?o ?e complete-shuffle? ] |
     [ ?o ?e ?i nths [ ==! ] 2map ]
   }

CHR{ { Pops ?s ?i } { Pushes ?t ?o } { Shuffle ?s ?t ?e } // -- |
     [ ?o ?e ?i nths [ ==! ] 2map ]
   }

CHR{ { Word ?s ?t curry } // -- |
     { Val ?s 0 ?p }
     { Val ?s 1 ?parm }
     { Val ?t 0 ?q }
     { Curried ?q ?parm ?p }
   }

CHR{ { Word ?s ?t compose } // -- |
     { Val ?s 0 ?p }
     { Val ?s 1 ?parm }
     { Val ?t 0 ?q }
     { Composed ?q ?parm ?p }
   }

CHR{ { Word ?r ?t if } // -- |
     ! { SplitState ?r ?st ?sf }
     ! { InlineUnknown ?r ?t ? }
     ! { InlineCond ?sf ?t ?q ?c2 } { InlineCond ?st ?t ?p ?c1 }
     { InlineCond ?r ?t ?q ?c2 } { InlineCond ?r ?t ?p ?c1 }
     { Cond ?c1 { Not { Instance ?c \ f } } }
     { Cond ?c2 { Instance ?c \ f } }
     { Val ?r 0 ?q } { Val ?r 1 ?p } { Val ?r 2 ?c }
   }
;

! ** Syntactic expansion
CHRAT: expand-quot { InferDef InferToplevelQuot InferBetween }
IMPORT: call-stack
IMPORT: basic-stack
! IMPORT: infer-stack
! IMPORT: stack-ops
CHR{ { Lit ?p ?q } // { InlineUnknown ?s ?t ?p } -- | { InlineQuot ?s ?t ?q true } }
! TODO: inheritance!
CHR{ { Lit ?p ?q } // { InlineCond ?s ?t ?p ?c } -- | { InlineQuot ?s ?t ?q ?c } }
CHR{ // { InferDef ?w } -- [ ?w deferred? not ] |
     [| | state-in state-out :> ( si so )
      ?w def>> :> def
      ?w :> w
      {
          { Entry +top+ w }
          { InlineQuot +top+ +end+ def true }
          ! { InferToplevelQuot def }
          ! { InferBetween +top+ +end+ def }
      }
     ] }

CHR{ { InlineQuot ?s ?t ?q ?c } // -- | [| | new-state :> s0
                                      ! "sr" <term-var> :> sr
                                      {
                                          ! { CallFrame ?s s0 sr ?t }
                                          { CondJump ?s s0 ?c }
                                          { InferBetween ?s ?t s0 ?q }
                                          { Linkback ?s { s0 } }
                                      }
                                     ] }

CHR{ // { InferToplevelQuot ?q } -- |
     ! { CallFrame +top+ +end+ ?s ?t }
     ! { InlineQuot ?s ?t ?q }
     { InlineQuot +top+ +end+ ?q true }
   }
CHR{ { InferBetween ?r ?t ?s ?q } // -- [ ?q known? ] |
     { Infer ?s ?s ?q }
     ! [| | ?s seq-state :> sn { { Infer ?s sn ?q } } ]
   }

CHR{ { InferredBetween ?r ?u ?s ?r } { InlineQuot ?r ?u __ ?c } // -- |
     { CondRet ?r ?u ?c }
   }

CHR{ // { InferBetween ?r ?t ?s ?q } { Infer ?s ?x [ ] } -- |
     ! [ ?x ?t ==! ]
     { InferredBetween ?r ?t ?s ?x ?q }
   }

CHR{ // { InsertState ?r ?t ?s } { Linkback ?u ?a } -- [ { ?r ?t } ?a subseq? ] |
     [| | { ?r ?t } ?a subseq-start :> i
      ?s i 1 + ?a insert-nth :> a2
      { Linkback ?u a2 }
     ]
   }

! CHR{ // { Linkback ?r ?a } { LinkStates ?s ?t } -- [ ?s ?a in? ]
!      | [| | ?a ?t suffix :> a2 { Linkback ?r a2 } ] }

! Main inference advancer
CHR{ ! { BeginQuot ?r ?beg }
    { InferBetween ?r __ ?beg __ }
     // { Linkback ?r ?a }
     { Infer ?beg ?s ?q } -- [ ?q empty? not ] |
     [| | ?q unclip :> ( rest w ) ?s seq-state :> sn
      ?a sn suffix :> a2
      { { Exec ?s sn w }
        ! { LinkStates ?s sn }
        { Infer ?beg sn rest }
        { Linkback ?r a2 }
      }
     ] }
! CHR{ // { Exec ?s ?t ?w } -- [ ?w word? ]
!      | [ ?w deferred? { ExecUnknown ?s ?t ?w } { CheckExec ?s ?t ?w } ? ] }
CHR{ // { Exec ?s ?t ?w } -- [ ?w word? ] | { CheckExec ?s ?t ?w } }
CHR{ // { Exec ?s ?t ?w } -- [ ?w known? ] | { Push ?s ?t ?w } }
CHR{ // { ExecWord ?s ?t ?w } -- [ ?w inline? ]
     | [| | ?w def>> :> def { InlineCall ?s ?t ?w def } ] }
CHR{ // { InlineCall ?s ?t ?w ?d } -- | { Entry ?s ?w } { InlineQuot ?s ?t ?d true } }
CHR{ // { ExecWord ?s ?t ?w } -- | { Word ?s ?t ?w } }

CHR{ // { Word ?s ?t ?w } -- [ ?w generic? ] | { Generic ?s ?t ?w } }
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

: prepare-chrat-infer ( quot/word -- prog query )
    dup word?
    [ '{ { InferDef _ } } prepare-query ]
    [ '{ { InferToplevelQuot _ } } prepare-query ] if ;

: chrat-infer ( quot/word -- constraints )
    prepare-chrat-infer run-chr-query ;
    ! dup word?
    ! ! [ expand-quot swap '{ { InferDef _ } } run-chr-query ]
    ! [ '{ { InferDef _ } } run-chrat-query ]
    ! [ '{ { InferToplevelQuot _ } } run-chrat-query ] if ;
