USING: accessors arrays chr chr.factor chr.factor.compiler chr.factor.types
chr.factor.words chr.modular chr.parser chr.programs chr.state classes
combinators combinators.short-circuit continuations effects generalizations
generic kernel lists math math.order math.parser quotations sequences sets terms
types.util words ;

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


! Array, for collecting literals
TUPLE: NumLiterals < state-pred n ;

! TUPLE: FoldQuot < trans-pred missing lit-stack-in quot ;

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
TUPLE: InlineEffect < trans-pred quot ;
TUPLE: InlineCond < trans-pred val cond ;
TUPLE: InlineQuot < trans-pred quot ;
! TUPLE: InlineDip < InlineQuot quot saved ;
TUPLE: InlinedQuot < InlineQuot ;
TUPLE: BeginQuot < trans-pred ;
TUPLE: EndQuot < trans-pred ;
TUPLE: Infer < chr-pred beg s quot ;
TUPLE: InferToplevelQuot < chr-pred quot ;
TUPLE: InferDef < chr-pred word ;
TUPLE: InferDip < trans-pred in-stack quot ;
TUPLE: LinkStates < trans-pred ;
TUPLE: InsertState < trans-pred between ;
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
! CHR{ // { AddLink ?s ?t } { Linkback ?t ?a } -- | [ ?s ?a ?t prefix Linkback boa ] }

! Consolidate link sequences
CHR: propagate-linkback @ { Linkback ?r ?a } // { Linkback ?s ?b } -- [ ?s ?a in? ] |
! [| |
!  ?a ?b union :> c
 { Linkback ?r ?b }
! ]
    ;

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

! CHR{ { Effect ?x ?a ?b } // { Effect ?x ?a ?b } -- | }

! NOTE: This is tricky.  The idea is that any duplication is actually performed correctly on the stack?
! CHR: similar-effect-left @
!  { Dup ?x ?y } { Effect ?y L{ ?parm . ?a } ?b } // { Effect ?x ?c ?d } -- [ ?c known term-var? ] |
!      { Effect ?x L{ ?v . ?r } ?s }
!    ;

! CHR: copy-effect-left @
! { Dup ?x ?y } { Effect ?y ?a ?b } // -- [ ?a known term-var? ]
! | { Effect ?x ?c ?d } ;

! CHR: similar-effect-right @
! { Dup ?x ?y } { Effect ?x L{ ?parm . ?a } ?b } // { Effect ?y ?c ?d } -- [ ?c known term-var? ] |
! { Effect ?y L{ ?v . ?r } ?s }
!     ;

CHR: make-dup-right @ { Dup L{ ?a . ?b } ?y } // -- [ ?y known term-var? ] |
{ Dup L{ ?a . ?b } L{ ?c . ?d } } [ ?y L{ ?c . ?d } ==! ] ;

! CHR: propagate-dup-right @
! { Dup ?x L{ ?a . ?b } } // -- [ ?x known term-var? ] | [ ?x L{ ?c . ?d } ==! ] ;
! { Dup ?x L{ ?c . ?d } } // -- [ ?x known term-var? ] |
!   { Dup ?a ?c } { Dup ?b ?d } ;

! { Dup L{ ?a . ?b } L{ ?c . ?d } } [ ?x L{ ?a ?b } ==! ] ;
! CHR: propagate-dup-right @
! { Dup ?x ?y } // -- [ ?y known cons-state? ] | [ ?x L{ ?c . ?d } ==! ] ;

! CHR: propagate-dup-left @
! ! { Dup L{ ?a . ?b } ?y } // -- [ ?y atom? ] | [ ?y L{ ?c . ?d } ==! ] ;
! { Dup L{ ?a . ?b } ?y } // -- [ ?y known term-var? ] |
! { Dup ?a ?c } { Dup ?b ?d } ;
! { Dup L{ ?a . ?b } L{ ?c . ?d } } [ ?y L{ ?c ?d } ==! ] ;
! CHR: propagate-dup-left @
! { Dup ?x ?y } // -- [ ?x known cons-state? ] | [ ?y L{ ?c . ?d } ==! ] ;

CHR: destructure-dup @
// { Dup L{ ?a . ?b } L{ ?c . ?d } } -- [ ?b nil? not ] [ ?d nil? not ] | { Dup ?a ?c } { Dup ?b ?d } ;

CHR: literal-dup1 @
{ Lit ?x ?v } // { Dup ?x ?y } -- | { Lit ?y ?v } ;

CHR: literal-dup12 @
{ Lit ?y ?v } // { Dup ?x ?y } -- | { Lit ?x ?v } ;

! *** Dead Values
CHR{ // { Drop ?x } { Lit ?x __  } -- | { Dead ?x } }
CHR{ { Drop ?x } // -- | { Dead ?x } }

CHR: drop-lit1 @ { Dead ?x } // { Stack ?s L{ ?x . __ } } -- |  ;
CHR: drop-lit2 @ { Dead ?x } // { Lit ?x __ } -- | ;
CHR{ { Dead ?x } // { Instance ?x __ } -- | }

CHR{ { Dead ?x } // { Dead ?x } -- | }
CHR{ { Dead ?x } // { Effect ?x __ __ } -- | }


;

TERM-VARS: ?rho ?sig ;

! ** Effect Assumptions
CHRAT: basic-stack { Val Lit InferredEffect }
CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?a } -- | }

CHR: ask-val @ { Stack ?s ?v } // { ask { Val ?s ?n ?a } } --
[ ?n ?v llength* < ] | [ ?a ?n ?v lnth ==! ]
! { Val ?s ?n ?a }
{ entailed { Val ?s ?n ?a } }
    ;


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
CHR{ { Lit ?x ?a } // { Val ?s ?n ?x } { AskLit ?s ?n ?b } -- | [ ?b ?a ==! ] }
! CHR{ { Val ?s ?n ?x } { Lit ?x ?a } // { LitStack ?s ?v } { AskLit ?s ?n } -- |
!      [| | ?a ?n ?v new-nth :> v2 { LitStack ?s v2 } ]
!    }

! CHR{ { ask { LitStack ?s ?n ?v } } // -- { NumLiterals ?s 0 } }
! CHR{ { NumLiterals ?s ?n } {  }}
! CHR{ // { ask { LitStack ?s ?n } } }


CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?b } -- | [ ?b ?a ==! ] }
CHR{ { Stack ?s ?v } // { Stack ?s ?v } -- | }
CHR: same-stack @ { Stack ?s ?v } // { Stack ?s ?w } -- | [ ?v ?w ==! ] ;
! CHR: same-stack @ // { Stack ?s ?v } { Stack ?s ?w } -- | [ ?v ?w ==! ] ;
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
      ! Assume bivariable-effect in general!
      ?t {
           ! { [ ?e terminated?>> ] [ __ ] }
           ! { [ ?e bivariable-effect? ] [ o >list ?sig lappend ] }
           [ o >list ?sig lappend ]
      } cond Stack boa suffix
      ! {
      !     { [ ?e terminated?>> ] [ __ ] }
      !     { [ ?e bivariable-effect? ] [ o >list ?sig lappend ] }
      !     [ o >list ?rho lappend ] } cond InferredEffect boa suffix
     ] }

CHR: rem-trivial-jump @
! { CondJump ?r ?s true } // -- | { Stack ?r ?rho } { Stack ?s ?rho } }
 // { CondJump ?r ?s true } -- | [ ?r ?s ==! ] ;

CHR: rem-trivial-ret @
! { CondRet ?r ?s true } // -- | { Stack ?r ?rho } { Stack ?s ?rho } }
// { CondRet ?r ?s true } -- | [ ?r ?s ==! ] ;

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

CHR{ // { Push ?s ?t ?b } -- |
     { Lit ?v ?b }
     { Stack ?s ?rho }
     { Stack ?t L{ ?v . ?rho } }
   }

CHR{ { Lit ?a ?b } // -- |
     [ ?a ?b class-of Instance boa ] }


CHR: infer-dip @ // { Word ?s ?u dip } -- |
     { Stack ?s L{ ?q ?x . ?rho } }
     { Stack ?s0  ?rho }
     { AddLink ?s ?s0 }
     { InferCall ?s0 ?t ?q }
     { Stack ?t ?sig }
     { Stack ?u L{ ?x . ?sig } }
   ;

CHR{ // { Word ?s ?t call } -- |
     { Stack ?s L{ ?q . ?rho } }
     { Stack ?s0 ?rho }
     { AddLink ?s ?s0 }
     { InferCall ?s0 ?t ?q }
   }

TERM-VARS: ?crho ?csig ;
CHR: infer-call @ // { InferCall ?r ?u ?q } -- |
     ! { Effect ?q ?a ?b }
     { InlineUnknown ?r ?u ?q }
    ;

CHR: infer-dup @ // { Word ?s ?t dup } -- |
     { Stack ?s L{ ?x . ?rho } }
     { Stack ?t L{ ?y ?x . ?rho } }
     { Dup ?x ?y } ;

CHR: infer-over @ // { Word ?s ?t over } -- |
     { Stack ?s L{ ?y ?x . ?rho } }
     { Stack ?t L{ ?z ?y ?x . ?rho } }
     { Dup ?x ?z } ;

CHR: curry-effect @ // { Word ?s ?t curry } -- |
     { Stack ?s L{ ?p ?parm . ?rho } }
     { Effect ?p L{ ?parm . ?a } ?b }
     { Stack ?t L{ L{ ?parm . ?p } . ?rho } }
   ;

CHR{ // { Word ?s ?t compose } -- |
     { Stack ?s L{ ?q ?p . ?rho } }
     { Effect ?p ?a ?b }
     { Effect ?q ?b ?c }
     { Stack ?t L{ { ?p ?q } . ?rho } }
   }


CHR: assume-word-effect @ { Word ?s ?t ?w } // -- |
[| | ?w chrat-effect :> e { AssumeEffect ?s ?t e } ] ;

CHR: infer-shuffle @ // { Word ?s ?t ?w } -- [ ?w "shuffle" word-prop? [ linear-shuffle? ] [ f ] if* ] |
[ ?s ?t ?w "shuffle" word-prop shuffle-mapping Shuffle boa ] ;


! CHR{ // { Word ?s ?t ?w } -- [ ?w primitive? ] | { Prim ?s ?t ?w } }

CHR{ // { Word ?s ?t drop } -- |
     { Stack ?s L{ ?x . ?rho } }
     { Stack ?t ?rho }
     { Drop ?x } }

CHR{ // { Word ?s ?t nip } -- |
     { Stack ?s L{ ?y ?x . ?rho } }
     { Stack ?t L{ ?y . ?rho } }
     { Drop ?x }
   }

CHR{ // { Word ?s ?t pick } -- |
     { Stack ?s L{ ?z ?y ?x . ?rho } }
     { Stack ?t L{ ?w ?z ?y ?x . ?rho } }
     { Dup ?x ?w }
   }

TERM-VARS: ?st0 ?st1 ?sf0 ?sf1 ;

! *** Conditionals
! For now, let's set the input and output effects of the quotations to be the
! same.  The goal is to have things that are branch-independent in the common
! effect, while anything that is branch-dependent has to be queried using the
! logical system.
CHR: infer-if @ // { Word ?r ?t if } -- |
     { Stack ?r L{ ?q ?p ?c . ?rho } }

     { Cond ?c1 { Not { Instance ?c \ f } } }
     { CondJump ?r ?st0 ?c1 }
     { Stack ?st0 ?rho }
     ! { Effect ?p ?a ?b }
     { Effect ?p ?rho ?sig }
     { InlineUnknown ?st0 ?st1 ?p }
     ! { InferCall ?st0 ?st1 ?p }
     { CondRet ?st1 ?t ?c1 }

     { Cond ?c2 { Instance ?c \ f } }
     { Disjoint ?c1 ?c2 }
     { CondJump ?r ?sf0 ?c2 }
     { Stack ?sf0 ?rho }
     ! { Effect ?q ?x ?y }
     { Effect ?q ?rho ?sig }
     { InlineUnknown ?sf0 ?sf1 ?q }
     ! { InferCall ?sf0 ?sf1 ?q }
     { CondRet ?sf1 ?t ?c2 }

     ! { JoinStacks ?b ?d ?sig }

     ! { Effect ?p ?rho ?sig }
     ! { Effect ?q ?rho ?sig }
     { Stack ?t ?sig }

     ! { Linkback ?r { ?st0 } }
     ! { InlineUnknown ?s0 ?t ?q } { InlineUnknown ?s0 ?t ?p }
     ! { Val ?r 0 ?q } { Val ?r 1 ?p } { Val ?r 2 ?c }
   ;
;

! ** Cleanup
CHRAT: clean-states { RemoveState }
! CHR{ { RemoveState ?s } // { Linkback ?s ?a } -- |
!      [ ?a members [ RemoveState boa ] map ]
!    }
! CHR{ { RemoveState ?s } // { Linkback ?r ?a } -- [ ?s ?a known in? ] |
!      [ ?r ?s ?a remove Linkback boa ]
!    }
! CHR{ // { RemoveState ?s } { Stack ?s __ } -- | }
;

! ** Syntactic expansion
CHRAT: expand-quot { InferDef InferToplevelQuot InferBetween ChratInfer }
IMPORT: call-stack
IMPORT: data-flow
IMPORT: clean-states
IMPORT: basic-stack
IMPORT: chrat-types
IMPORT: chrat-words
! IMPORT: infer-stack
! IMPORT: stack-ops

CHR{ // { ChratInfer ?w } -- [ ?w word? ] | { InferDef ?w } }
! CHR{ // { ChratInfer W{ ?w } } -- | { InferDef ?w } }
CHR{ // { ChratInfer ?w } -- [ ?w callable? ] | { InferToplevelQuot ?w } }

! This is tricky...
! CHR{ { InlineUnknown ?s ?t ?q } { Dup ?p ?q } { Effect ?p ?a ?b } { Effect ?q L{ ?parm . __ } __ } // -- |
!      ! { Dup ?parm ?x }
!      ! { Dup ?x ?parm }
!      { Stack ?s L{ ?x . ?a } }
!      { Stack ?t ?b }
!    }
CHR{ { InlineUnknown ?s ?t ?p } // -- | { Effect ?p ?a ?b } { Stack ?s ?a } { Stack ?t ?b } }

CHR{ { Lit ?p ?q } // { InlineUnknown ?s ?t ?p } ! { Effect ?p __ __ }
     -- |
     { InlineQuot ?s ?t ?q }
     { Drop ?p }
   }

CHR: uncurry @ // { InlineUnknown ?s ?t L{ ?parm . ?p } } -- |
     { Stack ?s ?rho }
     { Stack ?s0 L{ ?parm . ?rho } }
     { AddLink ?s ?s0 }
     { InlineUnknown ?s0 ?t ?p }
    ;

CHR: uncompose @ // { InlineUnknown ?s ?u { ?p ?q } } -- |
     { InlineUnknown ?s ?t ?p }
     { AddLink ?s ?t }
     { InlineUnknown ?t ?u ?q } ;

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

CHR: end-infer @ // { InferBetween ?r ?t ?q } { Infer ?r ?x [ ] } -- |
{ Stack ?x ?rho } { Stack ?t ?rho }
     ! [ ?x ?t ==! ]
   ;

! Main inference advancer
! NOTE: We have to handle wrappers here already, because term substitution into
! quotations will make use of wrapping themselves
CHR: infer-step @
    { InferBetween ?r ?t __ }
    //
     { Infer ?r ?s ?q } -- [ ?q empty? not ] |
     [| | ?q unclip :> ( rest w ) ?s seq-state :> sn
      w wrapper?
      [ w wrapped>> :> x { Push ?s sn x } ]
      [ { Exec ?s sn w } ] if :> action
      { action
        { Infer ?r sn rest }
        { AddLink ?r sn }
      }
     ] ;

TUPLE: ApplyWordRules < trans-pred w ;

CHR{ // { Exec ?s ?t ?w } -- [ ?w word? ] | { CheckExec ?s ?t ?w } }

CHR{ // { Exec ?s ?t ?w } -- [ ?w known? ] | { Push ?s ?t ?w } }

CHR{ { ExecWord ?s ?t ?w } // -- [ ?w chrat-in-types ]
     | [ ?s ?w chrat-in-types >list AcceptTypes boa ] }

CHR{ // { ExecWord ?s ?t ?w } -- [ ?w inline? ] | { InlineWord ?s ?t ?w  } }

CHR{ // { InlineWord ?s ?t ?w } -- | [| | ?w def>> :> def { InlineCall ?s ?t ?w def } ] }

! Test 2dip with tri
! CHR{ // { ExecWord ?s ?t 2dip } -- | [| | \ 2dip def>> :> d
!                                       { InlineQuot ?s ?t  d } ] }


! CHR{ // { InlineCall ?s ?t ?w ?d } -- | { Entry ?s ?w } { InlineQuot ?s ?t ?d } }

CHR{ // { InlineCall ?s ?t ?w ?d } -- | { Entry ?s ?w }
     { ApplyWordRules ?s ?t ?w } }

CHR{ // { ExecWord ?s ?t ?w } -- | { Word ?s ?t ?w } }

CHR{ // { Word ?s ?t ?w } -- [ ?w generic? ] | { Generic ?s ?t ?w } }
CHR{ // { Word ?s ?t ?w } -- [ ?w method? ] | { Method ?s ?t ?w } }

CHR{ { Word ?s ?t ?w } // -- | { ApplyWordRules ?s ?t ?w } }

! CHR: instantiate-rules @ // { ApplyWordRules ?s ?t ?w } -- |
! [ ?s ?t ?w instantiate-word-rules ] ;

! Insert at least one dummy state to prevent hooking into the top node with Entry specs
CHR: instantiate-rules @ // { ApplyWordRules ?s ?t ?w } -- | { Stack ?s ?rho } { Stack ?s0 ?rho } { AddLink ?s ?s0 }
     [ ?s0 ?t ?w instantiate-word-rules ] ;

! CHR{ { Word ?s ?t ?w } { Stack ?s ?v } { Lit ?a ?b } // -- [ ?b ?v ]}
! Folding
CHR{ { Word ?s ?t ?w } // -- [ ?w foldable? ] |
     [| | ?s ?t ?w stack-effect in>> length [ ?w execute ] FoldQuot boa ] }

CHR{ { FoldQuot ?s __ ?m __ } // -- | { NumLiterals ?s ?m } }

CHR: do-fold @ // { Word ?s ?t __ } { FoldQuot ?s ?t __ ?q } { LitStack ?s ?v t } -- |
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

! : chrat-infer ( quot/word -- constraints )
!     prepare-chrat-infer run-chr-query ;
    ! dup word?
    ! ! [ expand-quot swap '{ { InferDef _ } } run-chr-query ]
    ! [ '{ { InferDef _ } } run-chrat-query ]
    ! [ '{ { InferToplevelQuot _ } } run-chrat-query ] if ;

! : constraints>body ( store -- constraint )
!     values rest
!     H{ } lift ! apply ground substs
!     ! [ defined-equalities-ds [ collect-vars ] with-variable-off ] keep <generator> ;
!     dup [
!         no-defined-equalities on
!         check-integrity
!         fresh
!         [ collect-vars ] keep
!         "1" .
!         check-integrity
!         "2" .
!         <generator>
!     ] with-term-vars
!     ;
!     ! [ fresh collect-vars ] keep <generator> ;

