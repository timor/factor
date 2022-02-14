USING: accessors arrays chr chr.factor chr.factor.words chr.parser chr.programs
chr.state classes combinators combinators.short-circuit continuations effects
generalizations kernel lists math math.order math.parser quotations sequences
sets terms types.util words ;

IN: chr.factor.quotations
FROM: syntax => _ ;

! * Quotation Inference
TERM-VARS: ?e ?i ?l ?o ?p ?q ?r ?s ?st ?sf ?t ?u ?a ?b ?c ?d ?n ?m ?v ?w ?x ?xs ?y ?z ?c1 ?c2 ;
TERM-VARS: ?s0 ;

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

TUPLE: In/Out < trans-pred in-vals out-vals ;

TUPLE: ShiftPush < trans-pred d ;
TUPLE: ShiftPop < trans-pred d ;

TUPLE: ShiftStack < trans-pred n-in n-out ;

TUPLE: Shuffle < trans-pred mapping ;
! That's a use-once
TUPLE: Same < trans-pred m n ;

! List, will be used together with assume-effect
TUPLE: Stack < state-pred vals ;

! Array, for collecting literals
TUPLE: LitStack < state-pred vals done? ;
TUPLE: NumLiterals < state-pred n ;

TUPLE: AskLit < state-pred n var ;

! TUPLE: FoldQuot < trans-pred missing lit-stack-in quot ;
TUPLE: FoldQuot < trans-pred missing quot ;

: elt-vars ( seq -- seq )
    [ swap dup pair? [ first ] when
      [ nip ] [ number>string "v" prepend ] if*
      uvar
      <term-var>
    ] map-index <reversed> ;

! CHRAT: stack-ops { LitStack }
CHRAT: stack-ops { }

! CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?b } -- [ ?b ?a == ] | }
CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?a } -- | }
CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?b } -- | [ ?b ?a ==! ] }
! CHR{ // { Val ?s ?n ?a } { Val ?s ?n ?b } -- | [ ?b ?a ==! ] }

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
TUPLE: InlineUnknown < trans-pred val cond ;
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
TUPLE: InferDip < trans-pred in-stack quot ;
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
! An In/Out also means that we can go backwards

! CHR{ { In/Out ?s ?u __ __ } // { Link ?r ?u } -- | { Link ?s ?u } }

! CHR{ { SplitState ?s ?s1 __ } // { Link ?s1 ?u } -- | { Link ?s ?u } }
! CHR{ { SplitState ?s __ ?s2 } // { Link ?s2 ?u } -- | { Link ?s ?u } }
CHR{ { CondJump ?s ?u __ } { Link ?r ?u } // -- | { Link ?s ?u } }

! Transitivity
CHR{ // { Link ?r ?s } { Link ?s ?t } -- | { Link ?r ?t } }
    ;

:: complete-shuffle? ( in out e -- ? )
    { [ e out [ length ] same? ]
      [ e supremum 1 + in length = ]
    } 0&& ;

TERM-VARS: ?rho ?sig ;

! ** Effect Assumptions
CHRAT: basic-stack { Val Lit InferredEffect }
CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?a } -- | }

! ! Catch questions for literal stack values
CHR{ // { NumLiterals ?s ?n } -- |
     [| |
      ?n [ "lit" uvar <term-var> ] replicate dup :> vars
      <reversed> [| v i | { AskLit ?s i v } ] map-index
      { LitStack ?s vars f } suffix

      ! ?n [| i | { AskLit ?s i } ] { } map-integers
      ! { LitStack ?s V{ } } prefix
     ] }

CHR{ // { LitStack ?s ?v f } -- [ ?v [ known? ] all? ] |
     [| |
         ?v [ known ] map :> v2
         { LitStack ?s v2 t } ] }

CHR{ { AskLit ?s ?n ?x } // -- | { Val ?s ?n ?i } }
! Priority!
CHR{ { Val ?s ?n ?x } { Lit ?x ?a } // { AskLit ?s ?n ?b } -- | [ ?b ?a ==! ] }
! CHR{ { Val ?s ?n ?x } { Lit ?x ?a } // { LitStack ?s ?v } { AskLit ?s ?n } -- |
!      [| | ?a ?n ?v new-nth :> v2 { LitStack ?s v2 } ]
!    }

! CHR{ { ask { LitStack ?s ?n ?v } } // -- { NumLiterals ?s 0 } }
! CHR{ { NumLiterals ?s ?n } {  }}
! CHR{ // { ask { LitStack ?s ?n } } }


CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?b } -- | [ ?b ?a ==! ] }
CHR{ { Stack ?s ?v } // { Stack ?s ?v } -- | }
CHR: same-stack @ { Stack ?s ?v } // { Stack ?s ?w } -- | [ ?v ?w ==! ] ;

CHR{ { Stack ?s ?v } { Val ?s ?n ?a } // -- [ ?n ?v llength* < ] |
     [ ?a ?n ?v lnth ==! ]
   }

CHR{ // { AssumeEffect ?s ?t ?e } -- |
     [| | ?e [ in>> ] [ out>> ] bi 2dup :> ( i o )
      [ length ] bi@ :> ( ni no )
      f
      i elt-vars :> i
      o elt-vars :> o
      ! i [ ?s swap Pops boa suffix ] unless-empty
      ! o [ ?t swap Pushes boa suffix ] unless-empty
      ! i ?s swap Pops boa suffix
      ! o ?t swap Pushes boa suffix

      ! ?s ?t i o In/Out boa suffix


      ! ?s ?t
      ?s i >list ?rho lappend Stack boa suffix
      ?t {
           { [ ?e terminated?>> ] [ __ ] }
           { [ ?e bivariable-effect? ] [ o >list ?sig lappend ] }
           [ o >list ?rho lappend ]
      } cond Stack boa suffix
      ! {
      !     { [ ?e terminated?>> ] [ __ ] }
      !     { [ ?e bivariable-effect? ] [ o >list ?sig lappend ] }
      !     [ o >list ?rho lappend ] } cond InferredEffect boa suffix
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

CHR: rem-trivial-jump @
! { CondJump ?r ?s true } // -- | { Stack ?r ?rho } { Stack ?s ?rho } }
 // { CondJump ?r ?s true } -- | [ ?r ?s ==! ] ;

CHR: rem-trivial-ret @
! { CondRet ?r ?s true } // -- | { Stack ?r ?rho } { Stack ?s ?rho } }
// { CondRet ?r ?s true } -- | [ ?r ?s ==! ] ;

! Dip return
! TODO: Don't keep
! NOTE: Stack state at ?r includes the top-level element, but this will be replaced now?
! CHR{ { InferDip ?r ?u ?x __ } { InferredBetween ?r ?u ?s ?t __ } // { InferredEffect ?r ?u ?a ?d } { InferredEffect ?s ?t ?b ?c } -- |
!      { InferredEffect ?r ?s L{ ?x . ?rho } ?rho }
!      { InferredEffect ?t ?u ?sig L{ ?x . ?sig } }
!    }


! NOTE: changing this to be driven by marker predicate Stack
! CHR{ // { InferredEffect ?r ?s ?a ?b } { InferredEffect ?s ?t ?b ?c } -- |
!      { InferredEffect ?r ?t ?a ?c } }

! CHR{ { InferredEffect ?r ?s ?a ?b } { InferredEffect ?s ?t ?c ?d } // -- |
!      [ ?b ?c ==! ] }

: pos-var ( stack-var n -- var )
    [ name>> "_i" append ] dip number>string append
    <term-var> ;

CHR{ // { Shuffle ?s ?t ?m } -- [ ?m known? ] |
     [| | ?m known dup :> m
      ! dup length 1 - :> lo
      dup length :> lo
      [ f ]
      [
          supremum 1 + :> li
          ?s li [
              ! "i" swap number>string append "_" append uvar <term-var>
              ?s swap pos-var
          ] { } map-integers :> v-in
          v-in >list ?rho lappend Stack boa
          ?t m <reversed> [ li swap - 1 - v-in nth ] map >list ?rho lappend Stack boa 2array
      ] if-empty
     ]
   }

! CHR{ // { Shuffle ?s ?t ?m } -- [ ?m known? ] |
!      [| | ?m known
!       dup length 1 - :> lo
!       dup supremum :> li
!       <reversed> [| ni no |
!        li ni - :> ni
!        ! l no - :> no
!        { Same ?s ?t ni no }
!       ] map-index ] }

! CHR{ { Val ?s ?i ?a } // { Same ?s ?t ?i ?o } { Val ?t ?o ?b } -- | [ ?a ?b ==! ] }

! CHR{ // { Shuffle ?s ?t ?e } -- [ ?e known? ] |
!      [| | ?e known in>> elt-vars :> in
!       ?e shuffle-mapping <reversed> [| ni no |
!                           ni in nth :> v
!                           { { Val ?s ni v }
!                               { Val ?t no v } }
!                          ] map-index concat ] }


! CHR{ { Pops ?s ?i } { Pushes ?t ?o } // { Shuffle ?s ?t ?e }  -- [ ?i ?o ?e complete-shuffle? ] |
!      [ ?o ?e ?i nths [ ==! ] 2map ]
!    }

! CHR{ { Pops ?s ?i } { Pushes ?t ?o } { Shuffle ?s ?t ?e } // -- |
!      [ ?o ?e ?i nths [ ==! ] 2map ]
!    }

! CHR{ { Pushes ?s ?l } // { ask { Val ?s ?n ?a } } -- [ ?n ?l length < ] | [ ?a ?n ?l nth ==! ] { entailed { Val ?s ?n ?a } } }

! CHR{ { Pushes ?s ?l } { Val ?s ?n ?a } // -- [ ?n ?l length < ] | [ ?a ?n ?l nth ==! ] }

! CHR{ // { Pushes ?s ?l } -- [ ?l known? ] | [ ?l known [| a i | ?s i a Val boa ] map-index ] }

! CHR{ { Pops ?s ?l } { Val ?s ?n ?a } // -- [ ?n ?l length < ] | [ ?a ?n ?l nth ==! ] }

! CHR{ // { Pops ?s ?l } -- [ ?l known? ] | [ ?l known [| a i | ?s i a Val boa ] map-index ] }

! CHR{ // { Pushes ?s ?t ?a } -- | [ ?a [ f ] [| seq | seq unclip :> ( rest e ) ?s sub-state :> s1 { { Pushes s1 ?t rest } { Push ?s s1 e } } ] if-empty ] }
! CHR{ // { Push ?s ?t { ?a ?u } } -- | { Push ?s ?t ?a } { Instance ?a ?u } }
CHR{ // { Push ?s ?t ?b } -- |
     { Lit ?v ?b }
     { AssumeEffect ?s ?t ( -- v ) }
     { Val ?t 0 ?v }
     ! { InferredEffect ?s ?t ?rho L{ ?v . ?rho } }

   }

CHR{ { Lit ?a ?b } // -- |
     [ ?a ?b class-of Instance boa ] }


CHR: assume-word-effect @ { Word ?s ?t ?w } // -- |
[| | ?w chrat-effect :> e { AssumeEffect ?s ?t e } ] ;

! FIXME: Have to make sure InlineQuot comes first because of replacement foo not working correctly right now
! Ideal fix: queue-based runner, so that we always see all var instances!
! CHR{ { Word ?s ?t dip  } // -- | { Val ?s 1 ?a } { Val ?s 0 ?q } { InlineQuot ?s ?t ?q } { Val ?t 0 ?a } }
! CHR{ // { Word ?s ?t dip } -- | { InlineUnknown ?s ?t ?q } { Val ?s 1 ?a } { Val ?s 0 ?q } { Val ?t 0 ?a } }
! CHR{ // { Word ?s ?t dip } -- | { InferDip ?s ?t ?a ?q } { Val ?s 1 ?a } { Val ?s 0 ?q } { Val ?t 0 ?a } }
TERM-VARS: ?dipsig ;
CHR: infer-dip @ // { Word ?r ?u dip } -- |
     { Stack ?r L{ ?q ?x . ?rho } }
     { Stack ?s0 L{ ?q . ?rho } }
     { Linkback ?r { ?s0 } }
     { InferCall ?s0 ?t ?q }
     { Stack ?t ?dipsig }
     { Stack ?u L{ ?x . ?dipsig } }
   ;

CHR{ // { Word ?s ?t call } -- |
     { InferCall ?s ?t ?q } { Val ?s 0 ?q } }

TERM-VARS: ?call-rho ;
CHR: infer-call @ { InferCall ?r ?t ?q } // -- |
     { Stack ?r L{ ?q . ?call-rho } }
     { Stack ?s0 ?call-rho }
     ! Pseudoframe
     { Linkback ?r { ?s0 } }
     { InlineUnknown ?s0 ?t ?q true } ;

CHR: infer-shuffle @ // { Word ?s ?t ?w } -- [ ?w "shuffle" word-prop? ] |
     [ ?s ?t ?w "shuffle" word-prop shuffle-mapping Shuffle boa ] ;

CHR{ // { Word ?s ?t curry } -- |
     { Val ?s 0 ?p }
     { Val ?s 1 ?parm }
     { Val ?t 0 ?q }
     { Curried ?q ?parm ?p }
   }

! CHR: infer-curry @ { Curried ?p ?parm ?v } // { InferCall ?r ?u ?p } -- |
!     { Stack ?r L{ ?p . ?rho } }
!     { Stack ?s0 L{ ?v ?parm . ?rho } }
!     { Linkback ?r { ?s0 } }
!     { InferCall ?s0 ?u ?v }
!     ! { InlineUnknown ?s0 ?u ?v }
!     ;
CHR: infer-curry @ { Curried ?p ?parm ?v } // { InlineUnknown ?r ?u ?p ?c } -- |
    { Stack ?r ?rho }
    { Stack ?s0 L{ ?parm . ?rho } }
    { Linkback ?r { ?s0 } }
    ! { InferCall ?s0 ?u ?v }
    { InlineUnknown ?s0 ?u ?v ?c }
    ;

CHR{ // { Word ?s ?t compose } -- |
     { Val ?s 0 ?p }
     { Val ?s 1 ?parm }
     { Val ?t 0 ?q }
     { Composed ?q ?parm ?p }
   }

CHR: infer-if @ // { Word ?r ?t if } -- |
     { Stack ?r L{ ?q ?p ?c . ?rho } }
     { Stack ?s0 ?rho }
     { Linkback ?r { ?s0 } }
     { InlineUnknown ?s0 ?t ?q ?c2 } { InlineUnknown ?s0 ?t ?p ?c1 }
     { Cond ?c1 { Not { Instance ?c \ f } } }
     { Cond ?c2 { Instance ?c \ f } }
     ! { Val ?r 0 ?q } { Val ?r 1 ?p } { Val ?r 2 ?c }
   ;
;

! ** Syntactic expansion
CHRAT: expand-quot { InferDef InferToplevelQuot InferBetween }
IMPORT: call-stack
IMPORT: basic-stack
! IMPORT: infer-stack
! IMPORT: stack-ops
CHR{ { Lit ?p ?q } // { InlineUnknown ?s ?t ?p ?c } -- | { InlineQuot ?s ?t ?q ?c } }
! TODO: inheritance!
! CHR{ { Lit ?p ?q } // { InlineCond ?s ?t ?p ?c } -- | { InlineQuot ?s ?t ?q ?c } }
! CHR{ { Lit ?p ?q } // { InferCall ?s ?t ?p } -- | { InlineQuot ?s ?t ?q true } }
CHR{ // { InferDef ?w } -- [ ?w deferred? not ] |
     [| | state-in state-out :> ( si so )
      ?w def>> :> def
      ?w :> w
      {
          { Entry +top+ w }
          { InlineQuot +top+ +end+ def true }
      }
     ] }

CHR{ { InlineQuot ?s ?t ?q ?c } // -- | [| | new-state :> s0
                                      {
                                          { CondJump ?s ?s0 ?c }
                                          { InferBetween ?s ?t ?s0 ?q }
                                      }
                                     ] }

CHR{ // { InferToplevelQuot ?q } -- |
     { InlineQuot +top+ +end+ ?q true }
   }

CHR{ { InferBetween ?r ?t ?s ?q } // -- [ ?q known? ] |
     { Infer ?s ?s ?q }
     { Linkback ?r { ?s } }
   }

! ! Dip connection
! CHR{ { Lit ?p ?q } { InferDip ?r ?u ?a ?p } // -- | [| | new-state :> ?s0 { InferBetween ?r ?u ?s0 ?q } ] }

! Clean up unconditional inlining
! CHR{ // { InlineQuot ?r ?u ?q true } { CondJump ?r ?s true } { CondRet ?t ?u true } -- |
!      [ { ?r ?u } { ?s ?t } ==! ]
!    }

! CHR{ { InlineQuot ?r ?u __ ?c } { InferredBetween ?r ?u ?s ?t __ } // -- |
CHR{ { InlineQuot ?r ?u __ ?c } // { InferredBetween ?r ?u ?s ?t __ } -- |
     { CondRet ?t ?u ?c }
   }

CHR: end-infer @ // { InferBetween ?r ?t ?s ?q } { Infer ?s ?x [ ] } -- |
     ! [ ?x ?t ==! ]
     { InferredBetween ?r ?t ?s ?x ?q }
     { Stack ?x ?sig }
     ! { AssumeEffect ?s ?x ( -- ) }
   ;

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

! CHR{ // { Word ?s ?t ?w } -- [ ?w generic? ] | { Generic ?s ?t ?w } }

! CHR{ { Word ?s ?t ?w } { Stack ?s ?v } { Lit ?a ?b } // -- [ ?b ?v ]}
! Folding
CHR{ { Word ?s ?t ?w } // -- [ ?w foldable? ] |
     [| | ?s ?t ?w stack-effect in>> length [ ?w execute ] FoldQuot boa ] }

CHR{ { FoldQuot ?s __ ?m __ } // -- | { NumLiterals ?s ?m } }

CHR: do-fold @ // { FoldQuot ?s ?t __ ?q } { LitStack ?s ?v t } -- |
     ! [| | ?v ?q with-datastack :> res
     !  res <reversed> [| w i | "r" uvar <term-var> :> x { { Val ?t i x } { Lit x w } } ] map-index concat
     ! ]
     [| |
      ?v ?q with-datastack :> outs
      ?v length [ drop ] n*quot outs >quotation compose :> new-quot
      { InlineQuot ?s ?t new-quot true }
     ]
   ;

! CHR{ { Val ?s ?n ?a } { Lit ?a ?b } // { FoldQuot ?s ?t ?m ?v ?q } -- [ ?n ?m in? ] |
!      [| |
!       ?n ?m remove :> m2
!       ?b ?n ?v new-nth :> v2
!       { FoldQuot ?s ?t m2 v2 ?q }
!      ]
!    }
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
