USING: accessors arrays chr chr.factor chr.factor.conditions chr.factor.control
chr.factor.infer chr.factor.types chr.factor.words chr.modular chr.parser
chr.state combinators kernel lists math math.parser quotations sequences sets
terms types.util words ;

IN: chr.factor.quotations
FROM: syntax => _ ;

! * Quotation Inference



TUPLE: Prim < Word ;
TUPLE: InlineQuot < trans-pred quot ;
TUPLE: InferToplevelQuot < chr-pred quot ;
TUPLE: InferDef < chr-pred word ;
TUPLE: InferredBetween < trans-pred entry-state exit-state quot ;

! ** Data Flow
CHRAT: data-flow { Effect }

! Remove dropped literals
CHR{ // { Drop +top+ ?x } { Lit ?x __  } -- | { Dead ?x } }

! *** Sanity checks
CHR{ { Drop ?s ?x } { Drop ?s ?x } // -- | [ "double drop" throw ] }
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

;

! ** Basic stack handling
CHRAT: basic-stack { Lit InferredEffect }
! CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?a } -- | }


! CHR: ask-val @ { Stack ?s ?v } // { ask { Val ?s ?n ?a } } --
! [ ?n ?v llength* < ] | [ ?a ?n ?v lnth ==! ]
! ! { Val ?s ?n ?a }
! { entailed { Val ?s ?n ?a } }
!     ;

! CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?b } -- | [ ?b ?a ==! ] }
CHR{ { Stack ?s ?v } // { Stack ?s ?v } -- | }
CHR: same-stack @ { Stack ?s ?v } // { Stack ?s ?w } -- | [ ?v ?w ==! ] ;

! From condition system
CHR{ // { Cond +top+ P{ SameStack ?a ?b } } -- | [ ?a ?b ==! ] }
CHR{ // { Cond +top+ P{ Same ?x ?y } } -- | [ ?x ?y ==! ] }

! CHR: same-stack @ // { Stack ?s ?v } { Stack ?s ?w } -- | [ ?v ?w ==! ] ;
CHR: same-effect @ { Effect ?q ?i ?o } // { Effect ?q ?a ?b } -- | [ ?i ?a ==! ] [ ?o ?b ==! ] ;

! CHR{ { Stack ?s ?v } { Val ?s ?n ?a } // -- [ ?n ?v llength* < ] |
!      [ ?a ?n ?v lnth ==! ]
!    }

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
      ] if-empty ] }

CHR: make-push-stack @ // { Push ?s ?t ?b } -- |
     { Lit ?v ?b }
     { Stack ?s ?rho }
     { Stack ?t L{ ?v . ?rho } } ;

;

! ** Cleanup
! This runs after the condition system has marked everything absurd
TUPLE: CleanScope < chr-pred beg end ;

! This is only for cleanup
TUPLE: RemoveStack < chr-pred s ;

CHRAT: chrat-cleanup { }

! *** Dead Values
CHR{ { Dead ?x } // { Dead ?x } -- | }
! CHR{ // { Drop +top+ ?x } -- | { Dead ?x } }

! CHR: drop-lit1 @ { Dead ?x } // { Stack ?s L{ ?x . __ } } -- [ ?s known { +top+ +end+ } in? not ] |  ;
CHR: drop-lit2 @ { Dead ?x } // { Lit ?x __ } -- | ;
CHR{ { Dead ?x } // { Instance ?x __ } -- | }
!  CHR{ { Dead ?x } // { Cond __ P{ Instance ?x __ } } -- | }

CHR{ { Dead ?x } // { Effect ?x __ __ } -- | }
CHR{ { Dead ?x } // { Effect L{ ?x . __ } __ __ } -- | }

! *** Absurd States

! Stop inference
! CHR: abort-infer @ { AbsurdState ?r } // { InferBetween ?r __ __ } { Infer ?r __ __ } -- | ;


! Collect absurd values
! CHR: kill-absurd-stack-values @ { AbsurdState ?s } { Stack ?s ?v } // -- [ ?v known? ] |
!      [ ?v [ Dead boa ] collector [ leach* ] dip ]
!    ;

CHR: erase-absurd-state-preds @ { AbsurdState ?s } // SUB: ?x state-pred L{ ?s . __ } -- |
   [ ?x state-depends-on-vars [ Dead boa ] map ] ;
CHR: erase-absurd-trans-preds-1 @ { AbsurdState ?s } // SUB: ?x trans-pred L{ ?s . __ } -- | ;
CHR: erase-absurd-trans-preds-2 @ { AbsurdState ?s } // SUB: ?x trans-pred L{ __ ?s . __ } -- | ;

! This removes the AbsurdState marker!
! CHR: finish-absurd-state @ // { AbsurdState ?s } { Stack ?s __ } -- | ;
CHR: finish-absurd-state @ // { AbsurdState ?s } -- | ;


;


! ** Syntactic expansion, Inlining
CHRAT: expand-quot { InferDef InferToplevelQuot ChratInfer }
! IMPORT: control-flow
IMPORT: condition-prop
IMPORT: chrat-cleanup
IMPORT: data-flow
IMPORT: basic-stack
IMPORT: chrat-types
IMPORT: infer-factor
IMPORT: chrat-words

! ** Clean up Absurd artifacts

! We might have caused this exec to become absurd
! CHR{ { AbsurdState ?s } // { ExecWord ?s __ __ } -- | }
! CHR{ { AbsurdState ?s } // { Exec ?s __ __ } -- | }


! ** Cleanup
CHR{ { RemoveStack ?s } // { RemoveStack ?s } -- | }
CHR{ // { RemoveStack +top+ } -- | }
CHR{ // { RemoveStack +end+ } -- | }
CHR: clean-end-infer-scope @ { Scope ?r ?u ?l } // { EndInferScope ?s } -- [ ?s ?l in? ] | { CleanScope ?r ?u } ;
! CHR{ { Scope ?r ?u ?l } // { CleanScope ?s ?t } -- [ ?s ?l in? ] | { CleanScope ?r ?u } }
CHR: clean-scope-states @ { Scope ?s ?t ?l } // { CleanScope ?s ?t } -- [ ?l known? ] | [ ?l known members [ RemoveStack boa ] map ] ;

! This removes the RemoveStack marker!
CHR{ // { RemoveStack ?s } { Stack ?s __ } -- | }

! CHR{ { AbsurdScope ?s ?u } { Scope ?s ?u ?l } // SUB: ?x state-pred L{ ?t . __ } -- [ ?t ?l in? ] | }



! ** Inference
! Main inference advancer
! NOTE: We have to handle wrappers here already, because term substitution into
! quotations will make use of wrapping themselves



CHR: chrat-infer-def @ // { ChratInfer ?w } -- [ ?w word? ] | { InferDef ?w } ;

CHR: chrat-infer-top-quot @ // { ChratInfer ?w } -- [ ?w callable? ] | { InferToplevelQuot ?w } ;

! This is tricky...
! CHR{ { InlineUnknown ?s ?t ?q } { Dup ?p ?q } { Effect ?p ?a ?b } { Effect ?q L{ ?parm . __ } __ } // -- |
!      ! { Dup ?parm ?x }
!      ! { Dup ?x ?parm }
!      { Stack ?s L{ ?x . ?a } }
!      { Stack ?t ?b }
!    }
CHR: inline-unknown-effect @  { InlineUnknown ?s ?t ?p } // -- | { Effect ?p ?a ?b } { Stack ?s ?a } { Stack ?t ?b } ;

CHR: inline-made-known @  { Lit ?p ?q } // { InlineUnknown ?s ?t ?p } ! { Effect ?p __ __ }
     -- |
     { InlineQuot ?s ?t ?q }
     ! { Drop ?s ?p } ;
     { Drop +top+ ?p } ;

CHR: uncurry @ // { InlineUnknown ?s ?t L{ ?parm . ?p } } -- |
     { Stack ?s ?rho }
     { PrefixLink ?s ?s0 }
     { Stack ?s0 L{ ?parm . ?rho } }
     { InlineUnknown ?s0 ?t ?p } ;

CHR: uncompose @ // { InlineUnknown ?s ?u { ?p ?q } } -- |
     { PrefixLink ?s ?t }
     { InlineUnknown ?s ?t ?p }
     { InlineUnknown ?t ?u ?q } ;

CHR: infer-definition @  // { InferDef ?w } -- [ ?w deferred? not ] |
     [| | state-in state-out :> ( si so )
      ?w def>> :> def
      ?w :> w
      {
          { Entry +top+ w }
          { InlineQuot +top+ +end+ def }
      } ] ;

TERM-VARS: ?st0 ?st1 ?sf0 ?sf1 ;

! Conditionals
! For now, let's set the input and output effects of the quotations to be the
! same.  The goal is to have things that are branch-independent in the common
! effect, while anything that is branch-dependent has to be queried using the
! logical system.
CHR: infer-if @ // { Exec ?r ?t if } -- |
{ Stack ?r L{ ?q ?p ?c . ?rho } }
! { Stack ?st0 ?rho }
! { Stack ?sf0 ?rho }

{ Stack ?st0 ?a }
{ Stack ?st1 ?x }

{ Stack ?sf0 ?b }
{ Stack ?sf1 ?y }

! { Stack ?st1 ?sig }
! { Stack ?sf1 ?sig }


! NOTE: maybe this as same-val?
{ Stack ?t ?sig }
{ Branch ?r ?st0 ?sf0 }

{ Equiv ?st0 P{ Not P{ Instance ?c \ f } } }
{ CondJump ?r ?st0 }
! { Stack ?st0 ?rho }


! { Cond ?sf0 { Instance ?c \ f } }
{ Equiv ?sf0 P{ Instance ?c \ f } }

{ CondJump ?r ?sf0 }
{ Disjoint ?st0 ?sf0 }
! { Stack ?sf0 ?rho }


! { Stack ?st1 ?a }
{ Cond ?st0 P{ SameStack ?rho ?a } }
{ Cond ?st0 P{ SameStack ?x ?sig } }
! { CondRet ?st1 ?t }

{ Cond ?sf0 P{ SameStack ?rho ?b } }
{ Cond ?sf0 P{ SameStack ?y ?sig } }

! Do inference after conditions have been set up to ensure that absurdity is correctly used to remove alternatives!
{ InlineUnknown ?st0 ?st1 ?p }
{ InlineUnknown ?sf0 ?sf1 ?q } ;

CHR: infer-dip @ // { Exec ?s ?u dip } -- |
{ Stack ?s L{ ?q ?x . ?rho } }
{ PrefixLink ?s ?s0 }
{ Stack ?s0  ?rho }
{ Stack ?t ?sig }
{ Stack ?u L{ ?x . ?sig } }
{ InlineUnknown ?s0 ?t ?q }
    ;

CHR: exec-call @ // { Exec ?s ?t call } -- |
     { Stack ?s L{ ?q . ?rho } }
     { PrefixLink ?s ?s0 }
     { Stack ?s0 ?rho }
     { InlineUnknown ?s0 ?t ?q } ;

! We have to split this, because the in-types can already make this execword absurd
CHR: exec-early-types @ { ExecWord ?s ?t ?w } // -- [ ?w chrat-in-types ]
     | [ ?s ?w chrat-in-types >list AcceptTypes boa ] ;

CHR: exec-early-types @ { ExecWord ?s ?t ?w } // -- [ ?w chrat-out-types ]
     | [ ?s ?w chrat-out-types >list ProvideTypes boa ] ;

CHR: exec-inline-word @ // { ExecWord ?s ?t ?w } -- [ ?w inline? ] | { InlineWord ?s ?t ?w  } ;

! TUPLE: CheckInlineQuot < InlineQuot ;
! TUPLE: InliningDead < InlineQuot ;

CHR{ // { InlineCall ?s ?t ?w ?d } -- | { Entry ?s ?w }
     ! { ApplyWordRules ?s ?t ?w }
     ! For now be eager
     { InlineQuot ?s ?t ?d }
     ! { CheckInlineQuot ?s ?t ?d }
   }

! CHR{ { ConflictState ?s __ __ } // { CheckInlineQuot ?s ?t ?d }  -- | { InliningDead ?s ?t ?d } }
! CHR{ // { CheckInlineQuot ?s ?t ?d }  -- | { InlineQuot ?s ?t ?d } }

CHR: check-exec @ // { Exec ?s ?t ?w } -- [ ?w word? ] | { CheckExec ?s ?t ?w } ;

CHR: exec-push @ // { Exec ?s ?t ?w } -- [ ?w known? ] | { Push ?s ?t ?w } ;

CHR: inline-quot @ // { InlineQuot ?s ?t ?q } -- | { InferBetween ?s ?t ?q } ;

CHR: inline-top-quot @ // { InferToplevelQuot ?q } -- | { InlineQuot +top+ +end+ ?q } ;

! Hand off to the word-specific stuff
CHR: regular-word @ // { ExecWord ?s ?t ?w } -- | { Word ?s ?t ?w } ;

! Those are basically hooks

! CHR{ // { AbsurdScope __ __ __ } -- | }
! CHR{ // { Trivial __ } -- | }
! CHR{ // { Dead __ } -- | }
;
