USING: accessors chr chr.factor chr.factor.conditions chr.factor.control
chr.factor.data-flow chr.factor.infer chr.factor.stack chr.factor.types
chr.factor.words chr.parser chr.state kernel lists quotations sequences terms
words words.symbol ;

IN: chr.factor.quotations
FROM: syntax => _ ;

! * Quotation Inference



TUPLE: Prim < Word ;
TUPLE: InferToplevelQuot < chr-pred quot ;
TUPLE: InferDef < chr-pred word ;
TUPLE: InferredBetween < trans-pred entry-state exit-state quot ;

! ** Cleanup
! This runs after the condition system has marked everything absurd
! TUPLE: FinishScope < chr-pred beg end ;
TUPLE: FinishScope < chr-pred beg cont ;

! This is only for cleanup
TUPLE: RemoveStack < chr-pred s ;

CHRAT: chrat-cleanup { }

! *** Dead Values
CHR{ { Dead ?x } // { Dead ?x } -- | }
! CHR{ // { Drop +top+ ?x } -- | { Dead ?x } }

CHR: drop-lit2 @ { Dead ?x } // { Lit ?x __ } -- | ;
CHR{ { Dead ?x } // { Instance ?x __ } -- | }
!  CHR{ { Dead ?x } // { Cond __ P{ Instance ?x __ } } -- | }

CHR{ { Dead ?x } // { Effect ?x __ __ } -- | }
CHR{ { Dead ?x } // { Effect L{ ?x . __ } __ __ } -- | }
CHR: inlining-known @ { Dead ?p } // { InlinesUnknown __ ?p } -- | ;

! *** Absurd States

! Stop inference
! CHR: abort-infer @ { AbsurdState ?r } // { InferBetween ?r __ __ } { Infer ?r __ __ } -- | ;

! CHR: abort-infer-answer @ { AbsurdState ?r } // { ask { InferBetween ?r ?s ?q ?l } } -- |
! [ ?l f ==! ] { entailed { InferBetween ?r ?s ?q ?l } } ;
! CHR: abort-infer-step @ { AbsurdState ?r } // { InferBetween ?r __ __ __ } { Infer ?r __ __ } -- | ;

! Collect absurd values
! CHR: kill-absurd-stack-values @ { AbsurdState ?s } { Stack ?s ?v } // -- [ ?v known? ] |
!      [ ?v [ Dead boa ] collector [ leach* ] dip ]
!    ;

CHR: erase-absurd-state-preds @ { AbsurdState ?s } // SUB: ?x state-pred L{ ?s . __ } -- |
   [ ?x state-depends-on-vars [ Dead boa ] map ] ;
! CHR: erase-absurd-trans-preds-1 @ { AbsurdState ?s } // SUB: ?x trans-pred L{ ?s . __ } -- | ;
! CHR: erase-absurd-trans-preds-2 @ { AbsurdState ?s } // SUB: ?x trans-pred L{ __ ?s . __ } -- | ;

! This removes the AbsurdState marker!
! CHR: finish-absurd-state @ // { AbsurdState ?s } { Stack ?s __ } -- | ;
! CHR: finish-absurd-state @ // { AbsurdState ?s } -- | ;


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

TUPLE: RemoveStackops < chr-pred state ;
! We might have caused this exec to become absurd
! CHR{ { AbsurdState ?s } // { ExecWord ?s __ __ } -- | }
! CHR{ { AbsurdState ?s } // { Exec ?s __ __ } -- | }


! ** Cleanup
! CHR{ { RemoveStack ?s } // { RemoveStack ?s } -- | }
! CHR{ // { RemoveStack +top+ } -- | }
! CHR{ // { RemoveStack +end+ } -- | }
! CHR: clean-end-infer-scope @ { Scope ?r ?u ?l } // { EndInferScope ?s } -- [ ?s ?l in? ] | { FinishScope ?r ?u } ;
! CHR{ { Scope ?r ?u ?l } // { FinishScope ?s ?t } -- [ ?s ?l in? ] | { FinishScope ?r ?u } }
! CHR: clean-scope-states @ { Scope ?s ?t ?l } // { FinishScope ?s ?t } -- [ ?l known? ] | [ ?l known members [ RemoveStack boa ] map ] ;

! This removes the RemoveStack marker!
! CHR{ // { RemoveStack ?s } { Stack ?s __ } -- | }

! CHR{ { AbsurdScope ?s ?u } { Scope ?s ?u ?l } // SUB: ?x state-pred L{ ?t . __ } -- [ ?t ?l in? ] | }

CHR: finish-scope-stack-ops @  { Scope ?r ?u __ __ ?l } // { FinishScope ?r ?u } -- |
[ ?l known [ RemoveStackops boa ] map ]
    ;
! ! { StartStack ?r ?rho } { EndStack ?u ?sig } { FinishScope ?r ?u ?l } -- [ ?l last :>> ?t ]
! { FinishScope ?r ?u } -- [ ?l last :>> ?t ]
! ! { Stack ?t ?sig }
! |
! ! { Stack ?t ?sig }
! ! { Stack ?u ?sig }
! ! { StackOp ?r ?u ?rho ?sig }
! { StackOp ?r ?u ?rho ?sig }
! [ ?l [ RemoveStackops boa ] map ]
! { Scope ?s ?t ?l } ;

CHR: remove-stackop @ { RemoveStackops ?s } // { StackOp ?s __ __ __ } -- | ;
CHR: remove-stack @ { RemoveStackops ?s } // { Stack ?s __ } -- | ;
CHR{ // { RemoveStackops __ } -- | }

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
! CHR: inline-unknown-effect @  { InlineUnknown ?s ?t ?p } // -- | { Effect ?p ?a ?b } { Stack ?s ?a } { Stack ?t ?b } ;
! CHR: inline-unknown-effect @  { InlineUnknown ?s ?t ?p } // --
! | { Effect ?p ?a ?b }
! ! { Stack ?t ?b }
! { StackOp ?s ?t ?a ?b }
!     ;

CHR: notice-inline-unknown @ { InlineUnknown ?s ?t ?p } // -- | { InlinesUnknown ?s ?p } ;

CHR: inline-made-known @  { Lit ?p ?q } // { InlineUnknown ?s ?t ?p } ! { Effect ?p __ __ }
     -- |
     ! { Stack ?s ?a }
     ! { Stack ?t ?b }
     ! { effect ?p }
     { InlineQuot ?s ?t ?q }
     ! { Drop ?s ?p } ;
     { Drop ?p } ;

CHR: uncurry @ // { InlineUnknown ?s ?t L{ ?parm . ?p } } -- |
     ! { Stack ?s ?rho }
     ! { PrefixLink ?s ?s0 }
     ! { Stack ?s0 L{ ?parm . ?rho } }
     { StackOp ?s ?s0 ?rho L{ ?parm . ?rho } }
     ! { Stack ?s ?rho }
     ! { PrefixLink ?s ?s0 }
     { Stack ?s0 L{ ?parm . ?rho } }
     { InlineUnknown ?s0 ?t ?p } ;

! TODO test
CHR: uncompose @ // { InlineUnknown ?s ?u { ?p ?q } } -- |
     ! { PrefixLink ?s ?t }
     { InlineUnknown ?s ?t ?p }
     { InlineUnknown ?t ?u ?q } ;

CHR: infer-definition @  // { InferDef ?w } -- [ ?w deferred? not ] |
     [| | state-in state-out :> ( si so )
      ?w def>> :> def
      ?w :> w
      {
          { Entry +top+ w }
          { Stack +top+ ?rho }
          { InlineQuot +top+ +end+ def }
      } ] ;

TERM-VARS: ?st0 ?st1 ?sf0 ?sf1 ;

TUPLE: CheckBranch < chr-pred branch-state in true-in true-out false-in false-out ;

! Conditionals
! For now, let's set the input and output effects of the quotations to be the
! same.  The goal is to have things that are branch-independent in the common
! effect, while anything that is branch-dependent has to be queried using the
! logical system.
CHR: infer-if @ { Exec ?r ?t if } // --
{ Stack ?r L{ ?q ?p ?c . ?rho } }
|
! { Stack ?r L{ ?q ?p ?c . ?rho } }
{ Effect ?q ?a ?x }
{ Effect ?p ?b ?y }
! { CompatibleEffects ?a ?x ?b ?y }
! TODO: find best order
{ SameDepth ?rho ?a }
{ SameDepth ?rho ?b }
{ Split ?r ?rho ?a ?b }
{ Branch ?r ?t ?st0 ?sf0 }
{ Stack ?st0 ?a }
{ Stack ?st1 ?x }
{ Stack ?sf0 ?b }
{ Stack ?sf1 ?y }
{ InlineUnknown ?st0 ?st1 ?p }
{ InlineUnknown ?sf0 ?sf1 ?q }
{ Equiv ?st0 P{ Not P{ Instance ?c \ f } } }
{ Equiv ?sf0 P{ Instance ?c \ f } }
! { Stack ?t ?sig }
{ CheckBranch ?r ?rho ?a ?x ?b ?y }
    ;

CHR: end-infer-if @ // { Exec ?r ?t if } { CheckBranch ?r ?rho ?a ?x ?b ?y } --
{ CompatibleEffects ?a ?x ?b ?y }
|

{ SameDepth ?y ?sig }
{ SameDepth ?x ?sig }
{ Join ?r ?sig ?x ?y }
{ AssumeSameRest ?rho ?a }
{ AssumeSameRest ?y ?sig }
{ Stack ?t ?sig }
    ;

! Link-interface
CHR: link-branch-up @ { Branch ?r __ ?x __ } // { Link ?x ?u } -- | { Link ?r ?u } ;

CHR: infer-dip @ // { Exec ?s ?u dip } -- |
! { Stack ?s L{ ?q ?x . ?rho } }
! { PrefixLink ?s ?s0 }
! { Stack ?s0  ?rho }
{ StackOp ?s ?s0 L{ ?q ?x . ?rho } ?rho }
! { Stack ?t ?sig }
! { Stack ?u L{ ?x . ?sig } }
{ StackOp ?t ?u ?sig L{ ?x . ?sig } }
{ InlineUnknown ?s0 ?t ?q }
    ;

CHR: exec-call @ // { Exec ?s ?t call } -- |
     ! { Stack ?s L{ ?q . ?rho } }
     ! { PrefixLink ?s ?s0 }
     ! { Stack ?s0 ?rho }
{ StackOp ?s ?s0 L{ ?q . ?rho } ?rho }
{ InlineUnknown ?s0 ?t ?q } ;

! We have to split this, because the in-types can already make this execword absurd
CHR: exec-early-types @ { ExecWord ?s ?t ?w } // -- [ ?w chrat-in-types ]
     | [ ?s ?w chrat-in-types >list AcceptTypes boa ] ;

CHR: exec-early-types @ { ExecWord ?s ?t ?w } // -- [ ?w chrat-out-types ]
     | [ ?s ?w chrat-out-types >list ProvideTypes boa ] ;

CHR: exec-symbol-word @ // { ExecWord ?s ?t ?w } -- [ ?w symbol? ] | { Push ?s ?t ?w } ;

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

! ! CHR: check-exec @ // { Exec ?s ?t ?w } -- [ ?w word? ] | { CheckExec ?s ?t ?w } ;
CHR: exec-word @ // { Exec ?s ?t ?w } -- [ ?w word? ] | { ExecWord ?s ?t ?w } ;

CHR: exec-push @ // { Exec ?s ?t ?w } -- [ ?w known? ] | { Push ?s ?t ?w } ;

! CHR: inline-quot-start-stack @ { InlineQuot ?s ?t ?q } // -- |
! { StartStack ?s ?rho } ;
! ! { StackOp ?s ?t ?rho ?sig } ;

CHR: inline-quot @ // { InlineQuot ?s ?t ?q } --
| { InferBetween ?s ?t ?q }
! [ ?l last ?sig Stack boa ]
! { Stack ?t ?sig }
{ FinishScope ?s ?t } ;

CHR: inline-top-quot @ // { InferToplevelQuot ?q } -- |
{ Stack +top+ ?rho }
{ InlineQuot +top+ +end+ ?q }
    ;

! Hand off to the word-specific stuff
CHR: regular-word @ // { ExecWord ?s ?t ?w } -- | { Word ?s ?t ?w } ;

! Those are basically hooks

! CHR{ // { AbsurdScope __ __ __ } -- | }
! CHR{ // { Trivial __ } -- | }
CHR: finish-absurd-state @ // { AbsurdState ?s } -- | ;
CHR{ // { Dead __ } -- | }
;
