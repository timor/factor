USING: accessors arrays chr chr.factor chr.factor.compiler chr.factor.conditions
chr.factor.control chr.factor.types chr.factor.words chr.modular chr.parser
chr.state classes combinators combinators.short-circuit continuations effects
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

! CHR{ // { Linkback ?s ?a } { AddLink ?s ?t } -- | [ ?s ?a ?t suffix Linkback boa ] }
! CHR{ // { Linkback ?s ?a } { AddLink ?t ?b } -- [ ?t ?a known in? ] | [ ?s ?a ?b suffix Linkback boa ] }
! TODO Dangerous?
! CHR{ // { AddLink ?s ?t } { Linkback ?t ?a } -- | [ ?s ?a ?t prefix Linkback boa ] }

! Consolidate link sequences
! CHR: propagate-linkback @ { Linkback ?r ?a } // { Linkback ?s ?b } -- [ ?s ?a in? ] |
! ! [| |
! !  ?a ?b union :> c
!  { Linkback ?r ?b }
! ! ]
! ;

! CHR{ { Linkback ?r ?a } // { Linkback ?r ?b } -- [ ?b ?a subset? ] | }

! CHR{ // { Linkback ?r ?a } { Linkback ?r ?b } -- | [| | ?a ?b union :> c { Linkback ?r c } ] }

! CHR{ { Linkback ?s ?l } // { Link ?t ?u } -- [ ?s ?t == not ] [ ?t ?l in? ] | { Link ?s ?u } }

! CHR{ { CondJump ?s ?r __ } // { Link ?r ?u } -- | { Link ?s ?u } }

! Transitivity
! CHR{ // { Link ?r ?s } { Link ?s ?t } -- | { Link ?r ?t } }

;

:: complete-shuffle? ( in out e -- ? )
    { [ e out [ length ] same? ]
      [ e supremum 1 + in length = ]
    } 0&& ;

! ** Data Flow
CHRAT: data-flow { Effect }
! Sanity checks
CHR{ { Drop ?s ?x } { Drop ?t ?x } // -- | [ "double drop" throw ] }
! CHR{ { Dup ?x ?y } { Dup ?x ?y } // -- | [ "douple dup" throw ] }
CHR{ { Dup ?s ?x ?y } // { Dup ?s ?x ?y } -- | }
CHR{ { Dup __ ?x ?x } // -- | [ "self-dup" throw ] }

CHR{ // { Dup ?s ?x ?y } { Drop ?s ?y } -- | [ ?x ?y ==! ] }
CHR{ // { Dup ?s ?x ?y } { Drop ?s ?x } -- | [ ?x ?y ==! ] }

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

CHR: make-dup-right @ { Dup ?s L{ ?a . ?b } ?y } // -- [ ?y known term-var? ] |
{ Dup ?s L{ ?a . ?b } L{ ?c . ?d } } [ ?y L{ ?c . ?d } ==! ] ;

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
// { Dup ?s L{ ?a . ?b } L{ ?c . ?d } } -- [ ?b nil? not ] [ ?d nil? not ] | { Dup ?s ?a ?c } { Dup ?s ?b ?d } ;

CHR: literal-dup1 @
{ Lit ?x ?v } // { Dup __ ?x ?y } -- | { Lit ?y ?v } ;

CHR: literal-dup2 @
{ Lit ?y ?v } // { Dup __ ?x ?y } -- | { Lit ?x ?v } ;

! *** Dead Values
CHR{ { Dead ?x } // { Dead ?x } -- | }
! CHR{ // { Drop __ ?x } { Lit ?x __  } -- | { Dead ?x } }
CHR{ // { Drop +top+ ?x } -- | { Dead ?x } }

! CHR: drop-lit1 @ { Dead ?x } // { Stack ?s L{ ?x . __ } } -- [ ?s known { +top+ +end+ } in? not ] |  ;
CHR: drop-lit2 @ { Dead ?x } // { Lit ?x __ } -- | ;
CHR{ { Dead ?x } // { Instance ?x __ } -- | }

CHR{ { Dead ?x } // { Effect ?x __ __ } -- | }
CHR{ // { Dead __ } -- | }

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
! CHR{ // { NumLiterals ?s ?n } -- |
!      [| |
!       ?n [ "lit" uvar <term-var> ] replicate dup :> vars
!       <reversed> [| v i | { AskLit ?s i v } ] map-index
!       { LitStack ?s vars f } suffix

      ! ?n [| i | { AskLit ?s i } ] { } map-integers
      ! { LitStack ?s V{ } } prefix
!     ] }

! CHR{ // { LitStack ?s ?v f } -- [ ?v [ known? ] all? ] |
!      [| |
!          ?v [ known ] map :> v2
!          { LitStack ?s v2 t } ] }

! CHR{ { AskLit ?s ?n ?x } // -- | { Val ?s ?n ?i } }
! Priority!
! CHR{ { Lit ?x ?a } // { Val ?s ?n ?x } { AskLit ?s ?n ?b } -- | [ ?b ?a ==! ] }
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

! This is mainly useful for naming vars according to the declared effects...
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

! CHR: rem-trivial-jump @
! ! { CondJump ?r ?s true } // -- | { Stack ?r ?rho } { Stack ?s ?rho } }
!  // { CondJump ?r ?s true } -- | [ ?r ?s ==! ] ;

! CHR: rem-trivial-ret @
! ! { CondRet ?r ?s true } // -- | { Stack ?r ?rho } { Stack ?s ?rho } }
! // { CondRet ?r ?s true } -- | [ ?r ?s ==! ] ;

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
     { AddLink ?s ?s0 }
     { Stack ?s0  ?rho }
     { InferCall ?s0 ?t ?q }
     { Stack ?t ?sig }
     { Stack ?u L{ ?x . ?sig } }
   ;

CHR{ // { Word ?s ?t call } -- |
     { Stack ?s L{ ?q . ?rho } }
     { AddLink ?s ?s0 }
     { Stack ?s0 ?rho }
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
     { Dup ?s ?x ?y } ;

CHR: infer-over @ // { Word ?s ?t over } -- |
     { Stack ?s L{ ?y ?x . ?rho } }
     { Stack ?t L{ ?z ?y ?x . ?rho } }
     { Dup ?s ?x ?z } ;

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
     { Drop ?s ?x } }

CHR{ // { Word ?s ?t nip } -- |
     { Stack ?s L{ ?y ?x . ?rho } }
     { Stack ?t L{ ?y . ?rho } }
     { Drop ?s ?x }
   }

CHR{ // { Word ?s ?t pick } -- |
     { Stack ?s L{ ?z ?y ?x . ?rho } }
     { Stack ?t L{ ?w ?z ?y ?x . ?rho } }
     { Dup ?s ?x ?w }
   }

TERM-VARS: ?st0 ?st1 ?sf0 ?sf1 ;

! *** Conditionals
! For now, let's set the input and output effects of the quotations to be the
! same.  The goal is to have things that are branch-independent in the common
! effect, while anything that is branch-dependent has to be queried using the
! logical system.
CHR: infer-if @ // { Word ?r ?t if } -- |
     { Stack ?r L{ ?q ?p ?c . ?rho } }

     ! { Cond ?c1 { Not { Instance ?c \ f } } }
     { Cond ?st0 { Not { Instance ?c \ f } } }
     ! { CondJump ?r ?st0 ?c1 }
     { CondJump ?r ?st0 }
     { Stack ?st0 ?rho }
     ! { Effect ?p ?a ?b }
     ! { Effect ?p ?rho ?sig }
     { InlineUnknown ?st0 ?st1 ?p }
     ! { Stack ?st1 ?a }
     ! { InferCall ?st0 ?st1 ?p }
     ! { CondRet ?st1 ?t ?c1 }

     { CondRet ?st0 ?t }

     ! { Cond ?c2 { Instance ?c \ f } }
     { Cond ?sf0 { Instance ?c \ f } }
     ! { CondJump ?r ?sf0 ?c2 }
     { CondJump ?r ?sf0 }
     { Disjoint ?st0 ?sf0 }
     { Stack ?sf0 ?rho }
     ! { Effect ?q ?x ?y }
     ! { Effect ?q ?rho ?sig }
     { InlineUnknown ?sf0 ?sf1 ?q }
     ! { InferCall ?sf0 ?sf1 ?q }
     ! { CondRet ?sf1 ?t ?c2 }
     { CondRet ?sf0 ?t }
     ! { Stack ?sf1 ?b }

     ! { JoinStacks ?b ?d ?sig }

     ! { Effect ?p ?rho ?sig }
     ! { Effect ?q ?rho ?sig }
     ! { Stack ?t ?sig }

     ! { Linkback ?r { ?st0 } }
     ! { InlineUnknown ?s0 ?t ?q } { InlineUnknown ?s0 ?t ?p }
     ! { Val ?r 0 ?q } { Val ?r 1 ?p } { Val ?r 2 ?c }
   ;

! CHR: phi-stacks @
! // { CondRet ?a ?u } { CondRet ?b ?u } -- |
! { Stack ?a ?rho }
! { Stack ?b ?sig }
! { Cond ?a  }

;

! ** Cleanup
TUPLE: RemoveScope < trans-pred ;
TUPLE: RemoveState < state-pred ;

! Remove stack states of segments that are done
CHRAT: clean-states { RemoveScope RemoveState }

CHR{ { Scope ?s ?t ?l } // { RemoveScope ?s ?t } -- [ ?l known? ] | [ ?l known [ RemoveState boa ] map ] }
CHR{ // { RemoveState +top+ } -- | }
CHR{ // { RemoveState +end+ } -- | }
CHR{ // { RemoveState ?s } { Stack ?s __ } -- | }
;

! ** Syntactic expansion
CHRAT: expand-quot { InferDef InferToplevelQuot InferBetween ChratInfer }
! IMPORT: call-stack
IMPORT: control-flow
IMPORT: data-flow
! IMPORT: clean-states
IMPORT: condition-prop
IMPORT: basic-stack
IMPORT: chrat-types
IMPORT: chrat-words
IMPORT: clean-states
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
     { Drop ?s ?p }
   }

CHR: uncurry @ // { InlineUnknown ?s ?t L{ ?parm . ?p } } -- |
     { Stack ?s ?rho }
     { AddLink ?s ?s0 }
     { Stack ?s0 L{ ?parm . ?rho } }
     { InlineUnknown ?s0 ?t ?p }
    ;

CHR: uncompose @ // { InlineUnknown ?s ?u { ?p ?q } } -- |
     { AddLink ?s ?t }
     { InlineUnknown ?s ?t ?p }
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

CHR{ { InferBetween ?r ?t ?q } // -- [ ?q known? ] |
     { Stack ?r ?rho }
     { Stack ?s ?rho }
     { Scope ?r ?t { ?s } }
     { Infer ?r ?s ?q }
   }

CHR: end-infer @ // { InferBetween ?r ?t ?q } { Infer ?r ?x [ ] } -- |
{ Stack ?x ?rho } { Stack ?t ?rho }
{ RemoveScope ?r ?t }
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
        { AddLink ?r sn }
        { Infer ?r sn rest }
      }
     ] ;

TUPLE: ApplyWordRules < trans-pred w ;

CHR{ // { Exec ?s ?t ?w } -- [ ?w word? ] | { CheckExec ?s ?t ?w } }

CHR{ // { Exec ?s ?t ?w } -- [ ?w known? ] | { Push ?s ?t ?w } }

CHR{ { ExecWord ?s ?t ?w } // -- [ ?w chrat-in-types ]
     | [ ?s ?w chrat-in-types >list AcceptTypes boa ] }

CHR{ // { ExecWord ?s ?t ?w } -- [ ?w inline? ] | { InlineWord ?s ?t ?w  } }

CHR{ // { InlineWord ?s ?t ?w } -- | [| | ?w def>> :> def { InlineCall ?s ?t ?w def } ] }

TUPLE: CheckInlineQuot < InlineQuot ;
TUPLE: InliningDead < InlineQuot ;

CHR{ // { InlineCall ?s ?t ?w ?d } -- | { Entry ?s ?w }
     ! { ApplyWordRules ?s ?t ?w }
     ! For now be eager
     { CheckInlineQuot ?s ?t ?d }
   }

CHR{ { ConflictState ?s __ __ } // { CheckInlineQuot ?s ?t ?d }  -- | { InliningDead ?s ?t ?d } }
CHR{ // { CheckInlineQuot ?s ?t ?d }  -- | { InlineQuot ?s ?t ?d } }

CHR{ // { ExecWord ?s ?t ?w } -- | { Word ?s ?t ?w } }

! CHR{ { Word ?s ?t ?w } // -- [ ?w foldable? ] | { Stack ?s ?i } { Stack ?t ?o } { FoldCall ?s ?w ?i ?o } }

! CHR{ // { Word ?s ?t ?w } -- [ ?w generic? ] | { Generic ?s ?t ?w } }
! CHR{ // { Word ?s ?t ?w } -- [ ?w method? ] | { Method ?s ?t ?w } }

CHR{ { Word ?s ?t ?w } // -- [ ?w generic? not ] |
     { ApplyWordRules ?s ?t ?w } }

! Folding

TUPLE: FoldCall < Call ;
TUPLE: AskLit < Lit ;


! Alternatively, only try folding if we have a top literal?
CHR{ { Word ?s ?t ?w } { Stack ?s L{ ?x . __ } } { Lit ?x __ } // -- [ ?w foldable? ] |
     [| | ?w stack-effect in>> elt-vars dup
      >list ?rho lappend :> stack-in
      ! <reverse> [ number>string "lv" prepend uvar <term-var> 2array ] map :> var-map-in
      <reversed> dup :> var-in
      length [ number>string "lv" prepend uvar <term-var> ] { } map-integers :> lit-in
      ?w stack-effect out>> elt-vars dup
      >list ?sig lappend :> stack-out
      reverse :> var-out
      { { Stack ?s stack-in }
        { Stack ?t stack-out }
        { FoldCall ?s ?w lit-in var-out }
      }
      ! var-in [ number>string "lv" prepend uvar <term-var> AskLit boa ] map-index append
      var-in lit-in [ AskLit boa ] 2map append
     ]
   }

! Theoretically this is dead, because we don't expect a value to be used twice
CHR{ // { Lit ?x ?v } { AskLit ?x ?a } -- | [ ?a ?v ==! ] { Dead ?x } }

CHR: do-fold-call @ // { Call ?s __ __ __ } { FoldCall ?s ?w ?i ?o } -- [ ?i [ known? ] all? ] |
    [ ?i [ known ] map ?w 1quotation with-datastack
      ?o swap [ Lit boa ] 2map
] ;

! Anything else

CHR{ // { Word ?s ?t ?w } -- |
     { Stack ?s ?i }
     { Stack ?t ?o }
     { Call ?s ?w ?i ?o } }


! Insert at least one dummy state to prevent hooking into the top node with Entry specs
CHR: instantiate-rules @ // { ApplyWordRules ?s ?t ?w } -- | { Stack ?s ?rho } { Stack ?s0 ?rho } { AddLink ?s ?s0 }
     [ ?s0 ?t ?w instantiate-word-rules ] ;

! CHR{ { Word ?s ?t ?w } { Stack ?s ?v } { Lit ?a ?b } // -- [ ?b ?v ]}
! Folding
! Alternatively, only try folding if we have a top literal?
! CHR{ { Stack ?s L{ ?x . __ } } { Lit ?x __ } // { FoldCall ?s ?t ?w } -- |
!      [| | ?s ?t ?w stack-effect in>> length [ ?w execute ] FoldQuot boa ] }

! CHR{ { FoldQuot ?s __ ?m __ } // -- | { NumLiterals ?s ?m } }

! CHR: do-fold @ // { FoldQuot ?s ?t __ ?q } { LitStack ?s ?v t } -- |
!      ! [| | ?v ?q with-datastack :> res
!      !  res <reversed> [| w i | "r" uvar <term-var> :> x { { Val ?t i x } { Lit x w } } ] map-index concat
!      ! ]
!      [| |
!       ?v ?q with-datastack :> outs
!       ?v length [ drop ] n*quot outs >quotation compose :> new-quot
!       { InlineQuot ?s ?t new-quot }
!       ! { RemoveState ?s }
!      ]
!    ;
;
