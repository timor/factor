USING: accessors arrays chr chr.factor chr.factor.words chr.modular chr.parser
chr.programs chr.state classes combinators combinators.short-circuit
continuations effects generalizations kernel lists math math.order math.parser
quotations sequences sets terms types.util words ;

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

TUPLE: Uncons < chr-pred car cdr ;

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
TUPLE: InlineUnknown < trans-pred val ;
TUPLE: InlineEffect < trans-pred quot ;
TUPLE: InlineCond < trans-pred val cond ;
TUPLE: InlineQuot < trans-pred quot ;
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
TUPLE: InferBetween < trans-pred quot ;
TUPLE: InferredBetween < trans-pred entry-state exit-state quot ;
TUPLE: InferEffect < trans-pred in out quot ;
TUPLE: RemoveState < state-pred ;
TUPLE: AddLink < trans-pred ;

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

CHR{ { CheckExec ?t __ __ } // -- | { Link ?t ?t } }

CHR{ // { Linkback ?s ?a } { AddLink ?s ?t } -- | [ ?s ?a ?t suffix Linkback boa ] }
CHR{ // { Linkback ?s ?a } { AddLink ?t ?b } -- [ ?t ?a known in? ] | [ ?s ?a ?b suffix Linkback boa ] }
! TODO Dangerous?
CHR{ // { AddLink ?s ?t } { Linkback ?t ?a } -- | [ ?s ?a ?t prefix Linkback boa ] }

! CHR: propagate-linkback @ { Linkback ?r ?a } // { Linkback ?s ?b } -- [ ?s ?a in? ] |
! ! [| |
! !  ?a ?b union :> c
!  { Linkback ?r ?b }
! ! ]
!     ;

CHR{ { Linkback ?r ?a } // { Linkback ?r ?b } -- [ ?b ?a subset? ] | }

CHR{ // { Linkback ?r ?a } { Linkback ?r ?b } -- | [| | ?a ?b union :> c { Linkback ?r c } ] }

CHR{ { Linkback ?s ?l } // { Link ?t ?u } -- [ ?s ?t == not ] [ ?t ?l in? ] | { Link ?s ?u } }

CHR{ { CondJump ?s ?r __ } // { Link ?r ?u } -- | { Link ?s ?u } }

! Transitivity
CHR{ // { Link ?r ?s } { Link ?s ?t } -- | { Link ?r ?t } }
    ;

:: complete-shuffle? ( in out e -- ? )
    { [ e out [ length ] same? ]
      [ e supremum 1 + in length = ]
    } 0&& ;

! ** Data Flow
CHRAT: data-flow { Effect }
! Sanity checks
CHR{ { Drop ?x } { Drop ?x } // -- | [ "double drop" throw ] }
! CHR{ { Dup ?x ?y } { Dup ?x ?y } // -- | [ "douple dup" throw ] }
CHR{ { Dup ?x ?y } // { Dup ?x ?y } -- | }
CHR{ { Dup ?x ?x } // -- | [ "self-dup" throw ] }

CHR{ // { Dup ?x ?y } { Drop ?y } -- | [ ?x ?y ==! ] }
CHR{ // { Dup ?x ?y } { Drop ?x } -- | [ ?x ?y ==! ] }

! CHR{ { Dup ?x ?y } { Effect ?x ?a ?b } // -- | { Effect ?y ?c ?d }
!      { Dup ?a ?c } { Dup ?b ?d } }

! CHR{ { Dup ?x ?y } { Effect ?y ?c ?d } // -- | { Effect ?x ?a ?b }
!      { Dup ?a ?c } { Dup ?b ?d } }

! CHR{ { ask { Effect ?x ?a ?b } } { Dup ?x ?y } // -- | { Effect ?y ?c ?d } { Dup ?a ?c } { Dup ?b ?d } }
! CHR{ { ask { Effect ?y ?c ?d } } { Dup ?x ?y } // -- | { Effect ?x ?a ?b } { Dup ?a ?c } { Dup ?b ?d } }

CHR: propagate-dup-right @
{ Dup ?x L{ ?a . ?b } } // -- | [ ?x L{ ?c . ?d } ==! ] ;
! CHR: propagate-dup-right @
! { Dup ?x ?y } // -- [ ?y known cons-state? ] | [ ?x L{ ?c . ?d } ==! ] ;

CHR: propagate-dup-left @
{ Dup L{ ?a . ?b } ?y } // -- | [ ?y L{ ?c . ?d } ==! ] ;
! CHR: propagate-dup-left @
! { Dup ?x ?y } // -- [ ?x known cons-state? ] | [ ?y L{ ?c . ?d } ==! ] ;

CHR: destructure-dup @
// { Dup L{ ?a . ?b } L{ ?c . ?d } } -- | { Dup ?a ?c } { Dup ?b ?d } ;

CHR: literal-dup1 @
{ Lit ?x ?v } // { Dup ?x ?y } -- | { Lit ?y ?v } ;

CHR: literal-dup12 @
{ Lit ?y ?v } // { Dup ?x ?y } -- | { Lit ?x ?v } ;

CHR: drop-lit @ // { Drop ?x } { Lit ?x __ } { Instance ?x __ } { Stack __ L{ ?x . __ } } -- | ;
;

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
! CHR: same-stack @ { Stack ?s ?v } // { Stack ?s ?w } -- | [ ?v ?w ==! ] ;
CHR: same-stack @ { Stack ?s ?v } { Stack ?s ?w } // -- | [ ?v ?w ==! ] ;
CHR: same-effect @ { Effect ?q ?i ?o } // { Effect ?q ?a ?b } -- | [ ?i ?a ==! ] [ ?o ?b ==! ] ;

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

: affine-shuffle? ( mapping -- ? )
    duplicates empty? ;

: linear-shuffle? ( effect -- ? )
    [ in>> ] [ out>> ] bi { [ [ length ] same? ] [ set= ] } 2&& ;

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
     ! { AssumeEffect ?s ?t ( -- v ) }
     { Stack ?s ?rho }
     { Stack ?t L{ ?v . ?rho } }
     ! { Val ?t 0 ?v }
     ! { InferredEffect ?s ?t ?rho L{ ?v . ?rho } }

   }

CHR{ { Lit ?a ?b } // -- |
     [ ?a ?b class-of Instance boa ] }


! FIXME: Have to make sure InlineQuot comes first because of replacement foo not working correctly right now
! Ideal fix: queue-based runner, so that we always see all var instances!
! CHR{ { Word ?s ?t dip  } // -- | { Val ?s 1 ?a } { Val ?s 0 ?q } { InlineQuot ?s ?t ?q } { Val ?t 0 ?a } }
! CHR{ // { Word ?s ?t dip } -- | { InlineUnknown ?s ?t ?q } { Val ?s 1 ?a } { Val ?s 0 ?q } { Val ?t 0 ?a } }
! CHR{ // { Word ?s ?t dip } -- | { InferDip ?s ?t ?a ?q } { Val ?s 1 ?a } { Val ?s 0 ?q } { Val ?t 0 ?a } }
TERM-VARS: ?dipsig ;
CHR: infer-dip @ // { Word ?s ?u dip } -- |
     { Stack ?s L{ ?q ?x . ?rho } }
     ! { Stack ?s0 L{ ?q . ?rho } }
     { Stack ?s0 ?rho }
     { Effect ?q ?rho ?sig }
     { AddLink ?s ?s0 }
     { InferCall ?s0 ?t ?q }
     { Stack ?t ?sig }
     ! { Linkback ?s { ?u } }
     { Stack ?u L{ ?x . ?sig } }
     ! { Stack ?t ?dipsig }
     ! { Stack ?t L{ ?x . ?dipsig } }
   ;

CHR{ // { Word ?s ?t call } -- |
     { Stack ?s L{ ?q . ?rho } }
     { Stack ?s0 ?rho }
     { Effect ?q ?rho ?sig }
     { Stack ?t ?sig }
     { AddLink ?s ?s0 }
     { InferCall ?s0 ?t ?q }
     ! { InlineEffect ?s0 ?t ?q }
   }

TERM-VARS: ?crho ?csig ;
! FIXME: redundant
CHR: infer-call @ // { InferCall ?r ?u ?q } -- |
     ! { Stack ?r L{ ?q . ?rho } }
     ! { Effect ?q ?crho ?csig }
     ! { Stack ?s0 ?crho }
     ! ! Pseudoframe
     ! { Linkback ?r { ?s0 } }
     ! { InlineUnknown ?s0 ?u ?q } ;
     ! { Stack ?r L{ { ?rho ?sig } . ?crho } }
     ! { Stack ?u ?sig }
     ! { Stack ?s0 ?crho }
     ! Pseudoframe
     ! { Linkback ?r { ?s0 } }
     ! { InlineUnknown ?s0 ?t ?q }

     ! { InferEffect ?r ?u ?crho ?csig ?q }
     { InlineUnknown ?r ?u ?q }

     ! { InlineUnknown ?r ?u ?q }
     ! [ ?rho ?crho ==! ]
     ! [ ?sig ?csig ==! ]
    ;

CHR: infer-dup @ // { Word ?s ?t dup } -- |
     { Stack ?s L{ ?x . ?rho } }
     { Stack ?t L{ ?y ?x . ?rho } }
     { Dup ?x ?y } ;

CHR: infer-over @ // { Word ?s ?t over } -- |
     { Stack ?s L{ ?y ?x . ?rho } }
     { Stack ?t L{ ?z ?y ?x . ?rho } }
     { Dup ?x ?z } ;

! CHR{ // { Word ?s ?t curry } -- |
!      { Val ?s 0 ?p }
!      { Val ?s 1 ?parm }
!      { Val ?t 0 ?q }
!      { Curried ?q ?parm ?p }
!    }
CHR: curry-effect @ // { Word ?s ?t curry } -- |
     { Stack ?s L{ ?p ?parm . ?rho } }
     ! { Effect ?p L{ ?parm . ?a } ?b }
     ! { Effect ?p ?a ?b }
     ! { CurriedEffect ?q ?a ?b ?parm }
     ! { Effect ?q { uncons  } }
     { Stack ?t L{ L{ ?parm . ?p } . ?rho } }
     ! { Effect ?q ?c ?b }
     ! { Stack ?t L{ ?q . ?rho } }
   ;

CHR: assume-word-effect @ { Word ?s ?t ?w } // -- |
[| | ?w chrat-effect :> e { AssumeEffect ?s ?t e } ] ;

CHR: infer-shuffle @ // { Word ?s ?t ?w } -- [ ?w "shuffle" word-prop? [ linear-shuffle? ] [ f ] if* ] |
[ ?s ?t ?w "shuffle" word-prop shuffle-mapping Shuffle boa ] ;


CHR{ // { Word ?s ?t ?w } -- [ ?w primitive? ] | { Prim ?s ?t ?w } }

CHR{ // { Prim ?s ?t drop } -- |
     { Stack ?s L{ ?x . ?rho } }
     { Stack ?t ?rho }
     { Drop ?x } }

CHR: infer-curry @ { Curried ?p ?parm ?v } // { InlineUnknown ?r ?u ?p } -- |
    { Stack ?r ?rho }
    { Stack ?s0 L{ ?parm . ?rho } }
    ! { Linkback ?r { ?s0 } }
    ! { InferCall ?s0 ?u ?v }
    { InlineUnknown ?s0 ?u ?v }
    ;

CHR{ // { Word ?s ?t compose } -- |
     { Val ?s 0 ?p }
     { Val ?s 1 ?parm }
     { Val ?t 0 ?q }
     { Composed ?q ?parm ?p }
   }

TERM-VARS: ?st0 ?st1 ?sf0 ?sf1 ;

CHR: infer-if @ // { Word ?r ?t if } -- |
     { Stack ?r L{ ?q ?p ?c . ?rho } }

     { Cond ?c1 { Not { Instance ?c \ f } } }
     { CondJump ?r ?st0 ?c1 }
     { Stack ?st0 ?rho }
     { InlineUnknown ?st0 ?st1 ?p }
     { CondRet ?st1 ?t ?c1 }

     { Cond ?c2 { Instance ?c \ f } }
     { CondJump ?r ?sf0 ?c2 }
     { Stack ?sf0 ?rho }
     { InlineUnknown ?sf0 ?sf1 ?q }
     { CondRet ?sf1 ?t ?c2 }

     { Effect ?p ?rho ?sig }
     { Effect ?q ?rho ?sig }
     { Stack ?t ?sig }

     ! { Linkback ?r { ?st0 } }
     ! { InlineUnknown ?s0 ?t ?q } { InlineUnknown ?s0 ?t ?p }
     ! { Val ?r 0 ?q } { Val ?r 1 ?p } { Val ?r 2 ?c }
   ;
;

! ** Cleanup
! Find nearest link
! mark sweep
TUPLE: Mark < state-pred ;
! CHRAT: clean-states { RemoveState }
! CHR{ { RemoveState ?s } // { Linkback ?s ?a } -- |
!      [ ?a members [ RemoveState boa ] map ]
!    }
! CHR{ { RemoveState ?s } // { Linkback ?r ?a } -- [ ?s ?a known in? ] |
!      [ ?r ?a remove Linkback boa ]
!    }
! CHR{ { RemoveState ?s } // { Stack ?s __ } -- | }
! ;

! ** Syntactic expansion
CHRAT: expand-quot { InferDef InferToplevelQuot InferBetween }
IMPORT: call-stack
IMPORT: data-flow
! IMPORT: clean-states
IMPORT: basic-stack
! IMPORT: infer-stack
! IMPORT: stack-ops
CHR{ // { Lit ?p ?q } { InlineUnknown ?s ?t ?p } -- | { InlineQuot ?s ?t ?q } }
CHR: uncurry @ // { InlineUnknown ?s ?t L{ ?parm . ?p } } -- |
     { Stack ?s ?rho }
     { Stack ?s0 L{ ?parm . ?rho } }
     { AddLink ?s ?s0 }
     { InlineUnknown ?s0 ?t ?p } ;

! CHR{ { Effect ?p ?rho ?sig } // { InlineEffect ?s ?t ?p } -- |
!      { Stack ?s ?rho }
!      { InlineUnknown ?s ?t ?p }
!      { Stack ?t ?sig }
!    }
! TODO: inheritance!
! CHR{ { Lit ?p ?q } // { InlineCond ?s ?t ?p ?c } -- | { InlineQuot ?s ?t ?q ?c } }
! CHR{ { Lit ?p ?q } // { InferCall ?s ?t ?p } -- | { InlineQuot ?s ?t ?q true } }
CHR{ // { InferDef ?w } -- [ ?w deferred? not ] |
     [| | state-in state-out :> ( si so )
      ?w def>> :> def
      ?w :> w
      {
          { Entry +top+ w }
          { InlineQuot +top+ +end+ def }
      }
     ] }

CHR{ // { InlineQuot ?s ?t ?q } -- |
     ! [| | new-state :> s0
                                      ! {
                                          ! { CondJump ?s ?s0 true }
                                          { InferBetween ?s ?t ?q }
                                      ! }
   ! ]
}

CHR{ // { InferToplevelQuot ?q } -- |
     { InlineQuot +top+ +end+ ?q }
   }

CHR{ { InferBetween ?r ?s ?q } // -- [ ?q known? ] |
     { Infer ?r ?r ?q }
     { Linkback ?r { ?s } }
   }

! CHR: end-infer @ // { InferBetween ?r ?t ?q } { Infer ?r ?x [ ] } -- |
CHR: end-infer @ // { InferBetween ?r ?t ?q } { Infer ?r ?x [ ] } -- |
     [ ?x ?t ==! ]
     ! { InferredBetween ?r ?t ?s ?x ?q }
     ! { Stack ?x ?sig }
     ! { AssumeEffect ?s ?x ( -- ) }
   ;

! Main inference advancer
CHR{ ! { BeginQuot ?r ?beg }
    { InferBetween ?r ?t __ }
    //
    ! { Linkback ?r ?a }
     { Infer ?r ?s ?q } -- [ ?q empty? not ] |
     [| | ?q unclip :> ( rest w ) ?s seq-state :> sn
      ! ?a sn suffix :> a2
      { { Exec ?s sn w }
        ! { LinkStates ?s sn }
        { Infer ?r sn rest }
        { AddLink ?r sn }
      }
     ] }

! CHR{ // { Exec ?s ?t ?w } -- [ ?w word? ]
!      | [ ?w deferred? { ExecUnknown ?s ?t ?w } { CheckExec ?s ?t ?w } ? ] }
CHR{ // { Exec ?s ?t ?w } -- [ ?w word? ] | { CheckExec ?s ?t ?w } }
CHR{ // { Exec ?s ?t ?w } -- [ ?w known? ] | { Push ?s ?t ?w } }
CHR{ // { ExecWord ?s ?t ?w } -- [ ?w inline? ]
     | [| | ?w def>> :> def { InlineCall ?s ?t ?w def } ] }
CHR{ // { InlineCall ?s ?t ?w ?d } -- | { Entry ?s ?w } { InlineQuot ?s ?t ?d } }
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
      { InlineQuot ?s ?t new-quot }
      ! { RemoveState ?s }
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
