USING: accessors chr chr.comparisons chr.factor chr.factor.compiler
chr.factor.conditions chr.factor.control chr.factor.data-flow chr.factor.infer
chr.factor.stack chr.factor.types chr.factor.words chr.parser chr.state
sets
classes.error kernel lists quotations sequences sets.extras terms types.util
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

TUPLE: FinalizeInference < chr-pred ;

CHRAT: chrat-cleanup { }

! *** Dead Values
CHR: no-dead-lits @ // { Dead A{ __ } } -- | ;
CHR{ { Dead ?x } // { Dead ?x } -- | }
! CHR{ // { Drop +top+ ?x } -- | { Dead ?x } }

! NOTE: This does basically the same as the state-dep GC down below.
CHR: dead-var-type-vars-are-dead @ { Dead ?x } { Type ?x ?tau } // -- | { Dead ?tau } ;

CHR: drop-dead-val-preds @ { Dead ?x } //
<={ val-pred ?x . __ } -- | ;

CHR: drop-dead-type-preds @ { Dead ?x } //
<={ type-pred ?x . __ } -- | ;

CHR: drop-dead-eqs @ { Dead ?x } // { is ?x ?y } -- | ;

! *** Dead Phis

! *** Dead Conditions
! NOTE: condition values being dead means that they no longer can apply
CHR: drop-dead-cond-preds @ { Dead ?c } // <={ cond-pred ?c . __ } -- | ;

! TODO: sub-class-only matches
! CHR: dead-val-conds-are-dead @ { Dead ?v } // { Cond ?c ?p } -- [ p? known dup val-pred? [ value>>  ] [ drop f ] if ]
! CHR: dead-val-conds-are-dead @ { Dead ?v } // { Cond ?c <={ val-pred ?v . __ } } -- | ;
! CHR: dead-val-conds-are-dead @ { Dead ?v } // { Cond ?c ?p } -- [ ?p known ]
! [ ?p val-pred? [ ?p value>> ?v = ] [ ?p type-pred? [ ?p type>> ?v = ] [ f ] if ] if  ]
! | ;
! CHR: dead-type-conds-are-dead @ { Dead ?v } // { Cond ?c <={ type-pred ?v . __ } } -- | ;
! CHR{ { Dead ?x } // { Instance ?x __ } -- | }
!  CHR{ { Dead ?x } // { Cond __ P{ Instance ?x __ } } -- | }

! *** Dead Scopes
! CHR: dead-scopes-are-dead @ { Dead ?s } // SUB: ?x Scope L{ ?s __ __ __ ?l } |
CHR: dead-scopes-are-dead @ { Dead ?s } // <={ Scope ?s __ __ __ ?l . __ } -- |
[ ?l known [ Dead boa ] map ] ;

CHR: clean-dead-finish-scope @ { Dead ?r } // { FinishScope ?r ?u } -- | ;

! CHR{ { Dead ?x } // { Effect ?x __ __ } -- | }
! CHR{ { Dead ?x } // { Effect L{ ?x . __ } __ __ } -- | }
! CHR: inlining-known @ { Dead ?p } // { InlinesUnknown __ ?p } -- | ;
! CHR: inlining-known @ // { InlinesUnknown __ A{ __ } } -- | ;
CHR: inlining-known @ { is ?p A{ ?q } } // { InlinesUnknown __ ?p } -- | ;

! *** Dead quotations
CHR: no-dead-inlining @ { Dead ?q } // { InlineUnknown __ __ ?q } -- | ;
CHR: no-dead-inlining-1 @ { Dead ?q } // { InlinesUnknown __ ?q } -- | ;

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

! CHR: phi-dead-vars @ { EitherOr ?c ?c1 ?c2 }
! { --> ?c1 P{ is ?x ?a } } { --> ?c1 P{ Dead ?a } }
! { --> ?c2 P{ is ?x ?b } } { --> ?c2 P{ Dead ?b } } // -- |
! { --> ?c P{ Dead ?x } } ;

! ** Invalid stuff
CHR: cannot-create-invalid-values @ { Invalid ?v } { Call ?s ?t __ ?o } // --
[ ?o [ ?v = ] lany?* ] | { Impossible ?s } ;

CHR: cannot-define-invalid-values @ { Invalid ?v } { Def ?s ?v } // -- | { Impossible ?s } ;

CHR: impossible-true-branch @ { Not ?s } { Mux __ __ ?c __ ?q __ } // { Inlined ?s ?q } -- |
{ Not ?c } ;

CHR: impossible-false-branch @ { Not ?s } { Mux __ __ ?c __ __ ?q } // { Inlined ?s ?q } -- |
{ Fulfilled ?c } ;

CHR: invalid-scope-is-dead @ { Not ?s } AS: ?p <={ Scope ?s . __ } // -- | { Dead ?s } ;
;


! ** Syntactic expansion, Inlining
CHRAT: expand-quot { InferDef InferToplevelQuot ChratInfer }
IMPORT: chrat-comp
! IMPORT: control-flow
! IMPORT: condition-prop
IMPORT: entailment
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


! CHR: dead-branch-1 @ { Dead ?b } { Scope ?a ?x __ __ __ } // { Branch ?r ?u ?a ?b } -- | [ { ?r ?u } { ?a ?x } ==! ] ;

! CHR: dead-branch-2 @ { Dead ?a } { Scope ?b ?y __ __ __ } // { Branch ?r ?u ?a ?b } -- | [ { ?r ?u } { ?b ?y } ==! ] ;

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


CHR: chrat-infer-def @ // { ChratInfer ?w } -- [ ?w word? ] | { InferMode } { InferDef ?w } ;

CHR: chrat-infer-top-quot @ // { ChratInfer ?w } -- [ ?w callable? ] | { InferMode } { InferToplevelQuot ?w } ;

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

! CHR: inline-made-known @  { Lit ?p ?q } // { InlineUnknown ?s ?t ?p } ! { Effect ?p __ __ }
CHR: inline-made-known @ { is ?p A{ ?q } } // { InlineUnknown ?s ?t ?p } ! { Effect ?p __ __ }
     -- |
     { InlineQuot ?s ?t ?q }
     ! { Dead ?p }
     { Inlined ?s ?p }
    ;

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
          { FinalizeInference }
      } ] ;

TERM-VARS: ?true ?st1 ?false ?sf1 ;

! *** Specific words
CHR: infer-mux @ // { Exec ?r ?t ? } -- |
{ StackOp ?r ?t L{ ?q ?p ?x . ?rho } L{ ?y . ?rho } }
{ Mux ?r ?x ?c ?y ?p ?q }

{ --> ?c P{ is ?y ?p } }
{ \--> ?c P{ is ?y ?q } }

{ --> ?c P{ Not P{ is ?x W{ f } } } }
{ --> ?c P{ Drop ?q } }
{ \--> ?c P{ is ?x W{ f } } }
{ \--> ?c P{ Drop ?p } }
;

CHR: infer-if @ // { Exec ?r ?t if } -- { Stack ?r L{ ?q ?p ?c . ?rho } } |
{ InlineQuot ?r ?t [ ? call ] } ;

TUPLE: CheckBranch < state-pred in c1 c2 cond true-in true-out false-in false-out out ;

! Conditionals
! For now, let's set the input and output effects of the quotations to be the
! same.  The goal is to have things that are branch-independent in the common
! effect, while anything that is branch-dependent has to be queried using the
! logical system.
! CHR: infer-if @ // { Exec ?r ?t if } --
! ! { Stack ?r L{ ?q ?p ?c . ?rho } }
! |
! { Stack ?r L{ ?q ?p ?c . ?rho } }
! { Effect ?p ?a ?x }
! { Effect ?q ?b ?y }
! ! { CompatibleEffects ?a ?x ?b ?y }
! ! TODO: find best order
! ! { SameDepth ?rho ?a }
! ! { SameDepth ?rho ?b }
! ! { SplitStack ?rho ?a ?b }
! { Branch ?r ?t ?true ?false }
! { Stack ?true ?a }
! { Stack ?st1 ?x }
! { Stack ?false ?b }
! { Stack ?sf1 ?y }
! ! { Equiv ?true P{ Not P{ Instance ?c \ f } } }
! ! { Equiv ?false P{ Instance ?c \ f } }
! ! { Cond ?true P{ Not P{ Type ?c POSTPONE: f } } }
! ! { Cond ?false P{ Type ?c POSTPONE: f } }
! { EitherOr ?r ?c ?true ?false }
! ! { <--> ?false P{ is ?c W{ f } } }
! ! { --> ?true P{ is ?rho ?a } }
! ! { --> ?true P{ Drop ?q } }

! ! { --> ?false P{ is ?rho ?b } }
! ! { --> ?false P{ Drop ?p } }

! { --> ?true P{ is ?rho ?a } }
! { --> ?false P{ is ?rho ?b } }
! { --> ?true P{ Drop ?q } }

! { --> ?false P{ Drop ?p } }


! { InlineUnknown ?true ?st1 ?p }
! { InlineUnknown ?false ?sf1 ?q }
! ! { Stack ?t ?sig }
! { CheckBranch ?r ?true ?false ?c ?rho ?a ?x ?b ?y ?t }
!     ;

! CHR: end-infer-if @ // { CheckBranch ?r ?true ?false ?c ?rho ?a ?x ?b ?y ?t } --
! { CompatibleEffects ?a ?x ?b ?y }
! |

! ! { SameDepth ?y ?sig }
! ! { SameDepth ?x ?sig }
! ! { JoinStack ?sig ?x ?y }
! ! { AssumeSameRest ?rho ?a }
! ! { AssumeSameRest ?y ?sig }
! { <--> ?false P{ is ?c W{ f } } }
! { Stack ?t ?sig }
! { --> ?true P{ is ?sig ?x } }
! { --> ?false P{ is ?sig ?y } }
!     ;

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

! *** Phi inference
CHR: phi-inference @ { InlineUnknown ?r ?u ?q } { --> ?c P{ is ?q ?x } } { Effect ?x ?a ?b }
{ Effect ?q ?i ?o } // -- |
! { Scope ?s ?u ?i ?b { ?s0 ?u } }
! { Stack ?s0 ?a }
{ Jump ?r ?s }
! { --> ?c P{ is ?r ?s } }
! { --> ?c P{ is ?u ?t } }
{ InlineUnknown ?s ?t ?x } ;

! CHR: exhaustive-control-split @ { InlineUnknown __ __ ?a } { InlineUnknown __ __ ?b }
! { --> ?c P{ is ?q ?a } } { --> P{ Not ?c } P{ is ?q ?b } } // -- | { Dead ?q } ;

CHR: exhaustive-control-split @
! { InlineUnknown __ __ ?a } { InlineUnknown __ __ ?b }
! { --> ?c P{ is ?q ?a } } { --> P{ Not ?c } P{ is ?q ?b } } // { InlineUnknown __ __ ?q } -- | ;
{ --> ?c P{ is ?q ?a } } { --> P{ Not ?c } P{ is ?q ?b } } { InlineUnknown __ __ ?q } // -- | { Dead ?q } ;

! *** Types and Words

! We have to split this, because the in-types can already make this execword absurd
CHR: exec-early-types @ { ExecWord ?s ?t ?w } // -- [ ?w chrat-in-types ]
     | [ ?s ?w chrat-in-types >list AcceptTypes boa ] ;

CHR: exec-early-types @ { ExecWord ?s ?t ?w } // -- [ ?w chrat-out-types ]
     | [ ?t ?w chrat-out-types >list ProvideTypes boa ] ;

CHR: exec-error-word @ // { ExecWord ?s ?t ?w } -- [ ?w error-class? ] |
! { StackOp ?s ?t ?rho ?sig } ;
{ ConflictState ?s ?w "error" } ;

CHR: exec-symbol-word @ // { ExecWord ?s ?t ?w } -- [ ?w symbol? ] | { Push ?s ?t ?w } ;

CHR: exec-inline-word @ // { ExecWord ?s ?t ?w } -- [ ?w inline? ] | { InlineWord ?s ?t ?w  } ;

! TUPLE: CheckInlineQuot < InlineQuot ;
! TUPLE: InliningDead < InlineQuot ;

CHR: do-inline-call @ // { InlineCall ?s ?t ?w ?d } -- |
     { Entry ?s ?w }
     ! { ApplyWordRules ?s ?t ?w }

     ! For now be eager
     { InlineQuot ?s ?t ?d }
     ! { CheckInlineQuot ?s ?t ?d }
   ;

! TODO insert macro-expansion here!

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
{ FinishScope ?s ?t }
    ;

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
{ FinalizeInference }
    ;

! Hand off to the word-specific stuff
CHR: regular-word @ // { ExecWord ?s ?t ?w } -- | { Word ?s ?t ?w } ;

! Those are basically hooks

! CHR{ // { AbsurdScope __ __ __ } -- | }
! CHR{ // { Trivial __ } -- | }
CHR: finish-absurd-state @ // { AbsurdState ?s } -- | ;
! CHR{ // { Dead __ } -- | }

! ** Default Answers
! CHR: unknown-is-non-trivial @
! // { ask { IsTrivial ?p ?x } } -- | [ ?x f ==! ] { entailed { IsTrivial ?p ?x } } ;

! CHR: anything-is-possible @ // { ask { Possible ?c } } -- | { entailed { Possible ?c } } ;

! Don't do this during rule compilation, which will re-lift all top-level value predicates back to +top+ implications
CHR: fulfilment-by-default @ { InferMode } // { --> +top+ ?c } -- | { Fulfilled ?c } ;

! ** Finalizing

CHR: query-types @ { Scope +top+ +end+ ?rho ?sig __ } // -- |
[ ?rho list>array* ?sig list>array* union members
  [ "tau" uvar <term-var> Type boa ] map ] ;


! TODO Don't do this for enum-like structures! Also ensure that this is done at the very end!
CHR: uninteresting-exclusions @ { FinalizeInference } // { Not P{ is ?x A{ __ } } } -- | ;
CHR{ // { FinalizeInference } -- | }

;
