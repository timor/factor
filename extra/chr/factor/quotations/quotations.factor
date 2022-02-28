USING: accessors chr chr.factor chr.factor.conditions chr.factor.control
chr.factor.data-flow chr.factor.infer chr.factor.stack chr.factor.types
chr.factor.words chr.parser chr.state classes.error kernel lists quotations
sequences terms words words.symbol ;

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

! CHR: drop-lit2 @ { Dead ?x } // { Lit ?x __ } -- | ;
CHR: drop-dead-val-preds @ { Dead ?x } //
<={ val-pred ?x . __ } -- | ;

! *** Dead Phis
! CHR: trivial-split-1 @ { Branch ?r __ ?a ?b } { Dead ?b } // { SplitStack ?r ?x ?y ?z } -- | [ ?x ?y ==! ] ;
! CHR: trivial-split-2 @ { Branch ?r __ ?a ?b } { Dead ?a } // { SplitStack ?r ?x ?y ?z } -- | [ ?x ?z ==! ] ;
! CHR: trivial-join-1 @ { Branch ?r __ ?a ?b } { Dead ?b } // { JoinStack ?r ?x ?y ?z } -- | [ ?x ?y ==! ] ;
! CHR: trivial-join-2 @ { Branch ?r __ ?a ?b } { Dead ?a } // { JoinStack ?r ?x ?y ?z } -- | [ ?x ?z ==! ] ;

! *** Dead Conditions
! NOTE: condition values being dead means that they no longer can apply
CHR: drop-dead-cond-preds @ { Dead ?c } // <={ cond-pred ?c . __ } -- | ;

! TODO: sub-class-only matches
! CHR: dead-val-conds-are-dead @ { Dead ?v } // { Cond ?c ?p } -- [ p? known dup val-pred? [ value>>  ] [ drop f ] if ]
CHR: dead-val-conds-are-dead @ { Dead ?v } // { Cond ?c <={ val-pred ?v } } -- | ;
! CHR{ { Dead ?x } // { Instance ?x __ } -- | }
!  CHR{ { Dead ?x } // { Cond __ P{ Instance ?x __ } } -- | }

! CHR: dead-scopes-are-dead @ { Dead ?s } // SUB: ?x Scope L{ ?s __ __ __ ?l } |
CHR: dead-scopes-are-dead @ { Dead ?s } // <={ Scope ?s __ __ __ ?l . __ } -- |
[ ?l known [ Dead boa ] map ] ;

! CHR{ { Dead ?x } // { Effect ?x __ __ } -- | }
! CHR{ { Dead ?x } // { Effect L{ ?x . __ } __ __ } -- | }
CHR: inlining-known @ { Dead ?p } // { InlinesUnknown __ ?p } -- | ;

! *** Dead States

! CHR: dead-branches-are-dead { Dead ?s } // { Branch ?s ?t ?a ?b } -- |
! { Dead }

! CHR: erase-absurd-state-preds @ { AbsurdState ?s } // SUB: ?x state-pred L{ ?s . __ } -- |
CHR: dead-state-vars @ { Dead ?s } // AS: ?x <={ state-pred ?s . __ } -- |
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
[ ?l known [ RemoveStackops boa ] map ] ;


! CHR: dead-branch-1 @ { Branch ?r ?u ?a ?b } { Dead ?b } { Scope ?a ?x __ __ __ } // -- | [ { ?r ?u } { ?a ?x } ==! ] ;
! CHR: dead-branch-1 @ { Branch ?r ?u ?a ?b } { Dead ?b } { Scope ?a ?x ?rho ?sig ?l } // -- |
! { Scope ?r ?u ?rho ?sig ?l } ;

! CHR: dead-branch-2 @ { Branch ?r ?u ?a ?b } { Dead ?a } { Scope ?b ?y __ __ __ } // -- | [ { ?r ?u } { ?b ?y } ==! ] ;
! CHR: dead-branch-2 @ { Branch ?r ?u ?a ?b } { Dead ?a } { Scope ?b ?y ?rho ?sig ?l } // -- |
! { Scope ?r ?u ?rho ?sig ?l } ;

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
CHR: inline-unknown-effect @  { InlineUnknown ?s ?t ?p } // -- | { Effect ?p ?a ?b } { Stack ?s ?a } { Stack ?t ?b } ;
! CHR: inline-unknown-effect @  { InlineUnknown ?s ?t ?p } // --
! | { Effect ?p ?a ?b }
! ! { Stack ?t ?b }
! { StackOp ?s ?t ?a ?b }
!     ;

CHR: notice-inline-unknown @ { InlineUnknown ?s ?t ?p } // -- | { InlinesUnknown ?s ?p } ;
CHR: inline-unknown-curried @ // { InlinesUnknown ?c L{ ?x . ?xs } } -- | { InlinesUnknown ?c ?xs } ;

CHR: inline-made-known @  { Lit ?p ?q } // { InlineUnknown ?s ?t ?p } ! { Effect ?p __ __ }
     -- |
     ! { Stack ?s ?a }
     ! { Stack ?t ?b }
     ! { effect ?p }
     { InlineQuot ?s ?t ?q }
     ! { Drop ?s ?p } ;
     ! { Drop ?p } ;
     { Dead ?p } ;

CHR: uncurry @ // { InlineUnknown ?s ?t L{ ?parm . ?p } } -- |
     ! { Stack ?s ?rho }
     ! { PrefixLink ?s ?s0 }
     ! { Stack ?s0 L{ ?parm . ?rho } }
     { StackOp ?s ?s0 ?rho L{ ?parm . ?rho } }
     ! { Stack ?s ?rho }
     ! { PrefixLink ?s ?s0 }
     ! { Stack ?s0 L{ ?parm . ?rho } }
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

TUPLE: CheckBranch < state-pred in true-in true-out false-in false-out out ;

! Conditionals
! For now, let's set the input and output effects of the quotations to be the
! same.  The goal is to have things that are branch-independent in the common
! effect, while anything that is branch-dependent has to be queried using the
! logical system.
CHR: infer-if @ // { Exec ?r ?t if } --
! { Stack ?r L{ ?q ?p ?c . ?rho } }
|
{ Stack ?r L{ ?q ?p ?c . ?rho } }
{ Effect ?p ?a ?x }
{ Effect ?q ?b ?y }
! { CompatibleEffects ?a ?x ?b ?y }
! TODO: find best order
! { SameDepth ?rho ?a }
! { SameDepth ?rho ?b }
{ SplitStack ?r ?rho ?a ?b }
{ Branch ?r ?t ?st0 ?sf0 }
{ Stack ?st0 ?a }
{ Stack ?st1 ?x }
{ Stack ?sf0 ?b }
{ Stack ?sf1 ?y }
! { Equiv ?st0 P{ Not P{ Instance ?c \ f } } }
! { Equiv ?sf0 P{ Instance ?c \ f } }
! { Cond ?st0 P{ Not P{ Type ?c POSTPONE: f } } }
! { Cond ?sf0 P{ Type ?c POSTPONE: f } }
{ Equiv ?sf0 { = ?c f } }
{ Disjoint ?st0 ?sf0 }
{ InlineUnknown ?st0 ?st1 ?p }
{ InlineUnknown ?sf0 ?sf1 ?q }
! { Stack ?t ?sig }
{ CheckBranch ?r ?rho ?a ?x ?b ?y ?t }
    ;

CHR: end-infer-if @ // { CheckBranch ?r ?rho ?a ?x ?b ?y ?t } --
{ CompatibleEffects ?a ?x ?b ?y }
|

! { SameDepth ?y ?sig }
! { SameDepth ?x ?sig }
{ JoinStack ?r ?sig ?x ?y }
{ AssumeSameRest ?rho ?a }
{ AssumeSameRest ?y ?sig }
{ Stack ?t ?sig }
    ;

! Link-interface
CHR: link-branch-up @ { Branch ?r __ ?x __ } // { Link ?x ?u } -- | { Link ?r ?u } ;

CHR: infer-call @ // { Exec ?s ?u call } -- |
! { StackOp ?s ?s0 L{ ?q . ?rho } ?rho }
! { InlineUnknown ?s0 ?t ?q }
{ Scope ?s ?u L{ ?q . ?a } ?b { ?s0 ?t } }
! { Stack ?s L{ ?q . ?rho } }
! { Stack ?t ?sig }
{ Stack ?s L{ ?q . ?a } }
{ Stack ?s0 ?a }
{ Stack ?t ?b }
{ InlineUnknown ?s0 ?t ?q }
{ FinishScope ?s ?u }
    ;

CHR: infer-dip @ // { Exec ?s ?u dip } -- |
{ Scope ?s ?u L{ ?q ?x . ?a } L{ ?x . ?b } { ?s0 ?t } }
{ Stack ?s L{ ?q ?x . ?a } }
{ Stack ?s0 ?a }
{ Stack ?t ?b }
{ InlineUnknown ?s0 ?t ?q }
{ FinishScope ?s ?u }
    ;


! We have to split this, because the in-types can already make this execword absurd
CHR: exec-early-types @ { ExecWord ?s ?t ?w } // -- [ ?w chrat-in-types ]
     | [ ?s ?w chrat-in-types >list AcceptTypes boa ] ;

CHR: exec-early-types @ { ExecWord ?s ?t ?w } // -- [ ?w chrat-out-types ]
     | [ ?s ?w chrat-out-types >list ProvideTypes boa ] ;

CHR: exec-error-word @ // { ExecWord ?s ?t ?w } -- [ ?w error-class? ] |
! { StackOp ?s ?t ?rho ?sig } ;
{ ConflictState ?s ?w "error" } ;

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

CHR: clean-absurd-finish-scope @ { AbsurdScope ?r ?u __ } // { FinishScope ?r ?u } -- | ;

! CHR: simplify-dead-branch-1 @ { AbsurdScope ?c1 __ __ } { Scope ?c2 ?t __ __ __ } // { Branch ?r ?u ?c1 ?c2 } -- |
! [ { ?r ?u } { ?c2 ?t } ==! ] ;
! CHR: simplify-dead-branch-2 @ { Absurd ?c2 } { Scope ?c1 ?t __ __ __ } // { Branch ?r ?u ?c1 ?c2 } -- |
! [ { ?r ?u } { ?c1 ?t } ==! ] ;

! CHR: simplify-dead-branch-2 @ { AbsurdScope ?c2 __ __ } // { Scope ?c1 ?t ?rho ?sig ?l } { Branch ?r ?u ?c1 ?c2 } -- |
! { Scope ?r ?u ?rho ?sig ?l }
! [ ?r ?c1 ==! ] ;
! ! { Stack ?r ?rho }
! ! { Stack ?u ?sig }
! [ { ?r ?u } { ?c1 ?t } ==! ]
!    ;

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
! CHR{ // { Dead __ } -- | }

! Default Answers
! CHR: unknown-is-non-trivial @
! // { ask { IsTrivial ?p ?x } } -- | [ ?x f ==! ] { entailed { IsTrivial ?p ?x } } ;
;
