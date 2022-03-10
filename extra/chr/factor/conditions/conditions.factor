USING: accessors chr chr.comparisons chr.factor chr.parser chr.state classes
kernel sequences sets terms ;

IN: chr.factor.conditions

! * Condition system
! - Every Straightline inference has conditions attached to them
! - Any statement about values can be made conditional on that value

! Things that can be antecedents and consequents
MIXIN: test-pred
INSTANCE: val-pred test-pred
INSTANCE: Not test-pred
! This is left in the compiled constraints, so we can check whether there will
! be a recursive call
TUPLE: cond-pred < chr-pred cond ;
! TUPLE: state-cond < state-pred cond-pred ;
TUPLE: InlinesUnknown < cond-pred quot ;

! FIXME: Move!
TUPLE: Drop < val-pred ;

! Implication, or rather necessary conditions.
TUPLE: Cond < cond-pred implied ;

! Complement Implication
! This means that if the first condition is absurd, the second is also absurd
TUPLE: Necessary < cond-pred sub-cond ;

! TODO
TUPLE: Equiv < Cond ;
! TUPLE: Equiv < cond-pred c2 ;

! TUPLE: Disjoint < chr-pred c1 c2 ;
TUPLE: Disjoint < chr-pred members ;
TUPLE: SameStack < chr-pred s1 s2 ;
TUPLE: Same < chr-pred v1 v2 ;

TUPLE: ConflictState < chr-pred state but why? ;
! TUPLE: Absurd < chr-pred cond ;
TUPLE: Absurd < cond-pred ;
! TODO: make this a cond-pred??? And also the absurd one? Then replace absurdstate with dead-state!
TUPLE: Trivial < chr-pred cond ;
! TUPLE: CheckTrivial < chr-pred constraint ;
! TUPLE: IsTrivial < chr-pred cond ;
TUPLE: CondNest < chr-pred c1 c2 ;
! TODO: this should be a cond-pred, so that it will be propagated to the scope
! leader like regular
TUPLE: AbsurdState < chr-pred state ;
TUPLE: AbsurdScope < chr-pred beg end states ;
! TUPLE: AbsurdScope < Scope ;

! cond is either exactly fulfilled if alt1 is fulfilled or alt2 is fulfilled
! TUPLE: EitherOr < cond-pred alt1 alt2 ;
TUPLE: EitherOr < cond-pred cond-val alt1 alt2 ;
TUPLE: --> < cond-pred consequence ;
TUPLE: \--> < cond-pred consequence ;
TUPLE: <--> < cond-pred rhs ;

UNION: impl-pred --> \--> ;

! NOTE: This has assume/refute semantics.  This corresponds to open-word semantics,
! i.e. Anything is considered to be possible unless proven otherwise.
TUPLE: Assumed < cond-pred ;
TUPLE: Possible < cond-pred ;
TUPLE: Impossible < cond-pred ;
TUPLE: Fulfilled < cond-pred ;
TUPLE: Refuted < cond-pred ;

TUPLE: Redundant < chr-pred ;

! This couples a condition to a state, So that if the state is unreachable, the
! assumptions can be deleted.

! Destructure to make sure relevance is coupled
TUPLE: StateConstraint < chr-pred state constraint ;
! Capture Relevance
TUPLE: ScopeConds < cond-pred conds ;

! TODO move
TUPLE: AcceptType < state-pred val type ;
TUPLE: ProvideType < state-pred val type ;

CHRAT: entailment { }

! Probably expensive!
! *** Consistency
CHR: absurd-assumptions @ AS: ?p <={ test-pred } { Not ?p } // -- | { Inconsistent { ?p { Not ?p } } } ;

! *** Redundancies
CHR: duplicate-cond-pred @ AS: ?p <={ cond-pred ?x . ?y } // AS: ?q <={ cond-pred ?x . ?y } -- [ ?p ?q [ class-of ] same? ] | ;
CHR: duplicate-negation @ { Not ?p } // { Not ?p } -- | ;

CHR: redundant-exclusion @ { is ?x ?y } // { Not P{ is ?x __ } } -- | ;

CHR{ // { <--> ?x ?x } -- | }
CHR{ // { --> ?x ?x } -- | }

! *** Combination
CHR: same-if @ { EitherOr ?r ?c ?a ?b } // { EitherOr ?r ?c ?x ?y } -- | [ { ?a ?b } { ?x ?y } ==! ] ;
! *** Propagation

CHR: propagate-cond-preds-scope @
! { Scope ?s __ __ __ ?l }
<={ Scope ?r __ __ __ ?l . __ }
// AS: ?c <={ cond-pred ?s . __ } -- [ ?s ?l known in? ] |
[ ?c ?r >>cond ] ;

CHR: propagate-cond-preds-trans @ <={ trans-pred ?r ?s . __ } // AS: ?c <={ cond-pred ?s . __ }  -- |
[ ?c ?r >>cond ] ;

! *** Cleanup
CHR: will-be-dead @ { EitherOr ?r __ ?c1 ?c2 }
{ --> ?c1 P{ is ?x ?a } } { Dead ?a }
{ --> ?c2 P{ is ?x ?b } } { Drop ?b } // -- |
{ Dead ?x } ;

CHR: drop-dead-conds @ { Dead ?x } // <={ impl-pred __ ?p } -- [ ?p known test-pred? ] [ ?p known constraint-args first ?x == ] | ;
CHR: remove-unproven-assumptions @ { Impossible ?p } // { --> ?p __ } -- | ;
CHR: exclude-negative-assertions @ { Not ?p } // { --> ?p __ } -- | ;
CHR{ // { Fulfilled +top+ } -- | }
CHR{ { Dead ?q } // { --> __ ?q } -- | }

! CHR: same-value-assumption-must-be-same @ { --> ?c1 P{ is ?x ?a } } // { --> ?c1 P{ is ?x ?b } } -- |
! [ ?a ?b ==! ] ;

CHR: same-conditional-trait-must-be-same @ { --> ?c1 ?p } // { --> ?c1 ?q } --
[ ?p val-pred? ] [ ?q val-pred? ] [ ?p constraint-type ?q constraint-type = ] [ ?p value>> ?q value>> = ] |
[ ?q ?p ==! ] ;

! ** Reasoning
! *** Destructuring
! NOTE: Not completely sure if this is correct, also, maybe do this on the implication, not the equivalence?
CHR: negation-excludes-1 @ { EitherOr ?c __ ?c1 ?c2 } { <--> ?c1 ?p } // --
    [ ?p known Not? not ] | { <--> ?c2 P{ Not ?p } } ;
CHR: negation-excludes-2 @ { EitherOr ?c __ ?c1 ?c2 } { <--> ?c2 ?p } // --
    [ ?p known Not? not ] | { <--> ?c1 P{ Not ?p } } ;

CHR: destructure-equiv @ // { <--> ?p ?q } -- | { --> ?p ?q } { --> ?q ?p } ;
! CHR: convert-neg-test @ // { --> P{ Not ?p } ?q } -- | { \--> ?p ?q } ;
CHR: convert-neg-test @ // { \--> ?p ?q } -- | { --> P{ Not ?p } ?q } ;
! CHR: convert-double-neg-test @ // { \--> P{ Not ?p } ?q } -- | { --> ?p ?q } ;
CHR: convert-double-neg-test @ // { --> P{ Not P{ Not ?p } } ?q } -- | { --> ?p ?q } ;
CHR: convert-double-neg @ // { Not P{ Not ?p } } -- | { Fulfilled ?p } ;
CHR: back-propagate-impossible @ { --> ?p ?q } { Impossible ?q } // -- | { Impossible ?p } ;
CHR: exclude-middle-1 @ { EitherOr __ __ ?c1 ?c2 } { Fulfilled ?c1 } // -- | { Impossible ?c2 } ;
CHR: exclude-middle-2 @ { EitherOr __ __ ?c1 ?c2 } { Fulfilled ?c2 } // -- | { Impossible ?c1 } ;
CHR: disjunction-1 @ { Impossible ?c1 } // { EitherOr ?p __ ?c1 ?c2 } -- | { <--> ?p ?c2 } ;
CHR: disjunction-2 @ { Impossible ?c2 } // { EitherOr ?p __ ?c1 ?c2 } -- | { <--> ?p ?c1 } ;

! CHR{ { Impossible ?c2 } // -- [ ?c2 known chr-constraint? not ] | { Dead ?c2 } }
! CHR: propagate-fulfillment @ { Fulfilled ?q } { --> ?p ?q } // { --> ?q ?r } | { --> ?p ?r } ;
! CHR: propagate-fulfillment @ { --> ?p ?q } // { --> ?q ?r } -- { Fulfilled ?q } | { --> ?p ?r } ;

! *** Fulfilment

! These are store tests
! This is probably a kind of double negation check?

! CHR: redundant-implication-by-presence @ AS: ?x <={ val-pred __ . __ } // { --> __ ?q } --
! [ ?q ?x == ] | ;

! CHR: fulfilment-by-presence @ // { --> ?p ?q } AS: ?x <={ val-pred __ . __ } --
CHR: fulfilment-by-presence @ AS: ?x <={ test-pred __ . __ } // { --> ?p ?q } --
[ ?p ?x == ]
| { Fulfilled ?q } ;

CHR: negative-fulfillment-by-presence @ { Not ?p } // { \--> ?p ?q } -- | { Fulfilled ?q } ;
CHR: negative-redundancy-by-presence @ AS: ?p <={ test-pred } // { \--> ?p __ } -- | ;
! CHR: negative-redundancy-by-fulfillment @ { Fulfilled ?p } // { \--> ?p __ } -- | ;
CHR: negative-redundancy-by-fulfillment @ { Fulfilled ?p } // { --> P{ Not ?p } __ } -- | ;

CHR: assume-fullfillment @ { Fulfilled ?p } // { --> ?p ?q } -- | { Fulfilled ?q } ;

CHR: refute-by-atom-counterexample @ { --> ?c P{ is ?x A{ ?v } } } { is ?x A{ ?w } } // -- [ ?v ?w = not ] |
{ Impossible ?c } ;

! CHR: refute-by-negative-assertion @ AS: ?p <={ test-pred } { --> ?c P{ Not ?p } } // -- | { Not ?c } ;
CHR: refute-by-negative-assertion @ AS: ?p <={ test-pred } { --> ?c P{ Not ?p } } // -- | { Impossible ?c } ;

CHR: redundant-by-atom-counterexample @ { is ?x ?b } // { --> P{ is ?x ?c } __ } -- [ ?b ?c == not ] | ;

CHR: same-in-both @ { EitherOr ?p __ ?c1 ?c2 } { --> ?c1 ?p } { --> ?c2 ?p } // -- | { Fulfilled ?p } ;

CHR: enter-fulfilled @ // { Fulfilled ?q } -- [ ?q known chr-constraint? ] | [ ?q known ] ;

CHR: enter-impossible @ // { Impossible ?p } --
! [ ?p known chr-constraint? ]
| [ ?p known Not boa ] ;

! ** Simple Phi Stuff
! Reverse propagation of literals does not make sense
! CHR: propagate-literals-in @ { is ?x A{ ?v } } // { --> __ P{ is ?x ?y } } -- | { is ?y ?v } ;
! CHR: import-literals @ { is ?x A{ ?v } } // { --> ?c P{ is ?y ?x } } -- |
! { --> ?c P{ is ?y ?v } } ;
! CHR: propagate-dead @ { --> ?c P{ Dead ?y } } { --> ?c P{ is ?x ?y } } // -- | { --> ?c P{ Dead ?x } } ;

! NOTE: is this always valid? Should be, if we consider single-use semantics...
CHR: transitive-mux @ // { --> ?c P{ is ?x ?a } } { --> ?c P{ is ?y ?a } } -- | { --> ?c P{ is ?y ?x } } ;

CHR: assume-val-preds @ { --> ?c P{ is ?x ?a } } { --> ?c ?p } // -- [ ?p val-pred? ] [ ?p value>> ?a == ] [ ?p clone ?x >>value :>> ?q ] |
{ --> ?c ?q } ;

! *** General assumption
! CHR: phi-is-semi-lattice @ AS: ?r { impl-pred __ P{ is ?x ?a } } AS: ?p <={ val-pred ?a . __ } // -- [ ?a known term-var? ] |
! [ ?p constraint-type  ]
! { Assume  }
! { le ?q ?p } ;

;


! * Old implementation
CHRAT: condition-prop {  }

! NOTE: Potentially very expensive?
! CHR: presence-is-trivial @ // { CheckTrivial ?c } --
! [ store get [ nip constraint>> ?c = ] assoc-any? ] |
! { IsTrivial ?c } ;

! Redundancies
CHR: duplicate-cond-pred @ AS: ?p <={ cond-pred ?x . ?y } // AS: ?q <={ cond-pred ?x . ?y } -- [ ?p ?q [ class-of ] same? ] | ;

! CHR: duplicate-equiv @ { Equiv ?c ?p } // { Equiv ?c ?p } -- | ;

! Reverse dependencies to scopes
! FIXME: This kind of nesting will only work if matching is destructured completely during compilation
! CHR: analyze-state-constraint @ // { StateConstraint ?s AS: ?x <={ Cond ?c . __ } } -- |
! CHR: analyze-state-constraint @ // { StateConstraint ?s ?x } -- |
! { Necessary ?s ?c } [ ?x ] ;

! Destructure Predicates
! CHR: assume-condition @ // { Equiv ?x ?y } -- [ ?x known term-var? not ] [ ?y known term-var? not ] |
! { Equiv ?c ?x }
! { Equiv ?c ?y } ;
! CHR{ { Equiv ?x ?y } // -- [  ?x known term-var? not ] | { Equiv ?y ?x } }
! CHR: disjoint-complement @ // { Equiv ?x P{ Not ?c } } -- | { Equiv ?c1 ?c } { Disjoint ?x ?c1 } ;
! CHR: assume-implication @ // { Cond ?c ?p } -- [ ?c known term-var? not ] |
! { Equiv ?c2 ?c }
! { Cond ?c2 ?p } ;

! Conditional jump scope entries are the conditions!
! CHR: leader-is-cond-1 @ { CompileRule } { Linkback ?s ?v } // { Cond ?x ?c } -- [ ?x ?v known in? ] | { Cond ?s ?c }  ;

! Rewrite stuff to scope leaders
! CHR{ { Scope ?s __ ?l } // { Cond ?t ?k } -- [ ?t ?l known in? ] | { Cond ?s ?k } }
! CHR{ { Scope ?s __ ?l } // { Absurd ?t } -- [ ?t ?l known in? ] | { Absurd ?s } }
! CHR{ { Scope ?s __ ?l } // { Trivial ?t } -- [ ?t ?l known in? ] | { Trivial ?s } }

! CHR: propagate-cond-preds @ { Scope ?s __ ?l } // SUB: ?c cond-pred L{ ?x . ?xs } -- [ ?x ?l in? ] |
!     [ ?xs list>array ?s prefix ?c slots>tuple ] ;
! CHR: propagate-cond-preds-scope @ { Scope ?s __ __ __ ?l } // SUB: ?c cond-pred L{ ?x . __ } -- [ ?x ?l in? ] |
CHR: propagate-cond-preds-scope @
! { Scope ?s __ __ __ ?l }
<={ Scope ?r __ __ __ ?l . __ }
// AS: ?c <={ cond-pred ?s . __ } -- [ ?s ?c == not ] [ ?s ?l known in? ] |
    [ ?c ?r >>cond ] ;

CHR: propagate-cond-preds-trans @ <={ trans-pred ?r ?s . __ } // AS: ?c <={ cond-pred ?s . __ }  -- |
[ ?c ?r >>cond ] ;

! CHR: irrelevant-non-triviality @ // { IsTrivial __ f } -- | ;
! CHR: apply-trivial-absurdity @ { Cond ?c ?p } // { IsTrivial P{ Not ?p } } -- |
! { Absurd ?c } ;

! CHR: remove-trivial-cond @ // { IsTrivial ?p } { Cond __ ?p } -- | ;
! CHR: remove-trivial-cond @ // { IsTrivial ?p } { Cond __ ?p } -- | ;

! CHR{ { CheckTrivial ?p } // { CheckTrivial ?p } -- | }
! Test for triviality at least once
! CHR: ask-trivial-cond @ { Cond ?c ?p } // -- { CheckTrivial ?p } | ;
! CHR: ask-trivial-complement @ { Cond ?c P{ Not ?p } } // -- |
! { Cond ?c1 ?p }
! { Disjoint ?c ?c1 }
! { CheckTrivial ?p } ;

! CHR: ask-trivial-cond @ { Cond ?c ?p } // -- [ ?p known Not? not ] | { CheckTrivial ?p } ;

! CHR: complement-known @ { Cond ?c ?p } { Not ?p } // -- | { Absurd ?c } ;

! *** Testing cut-producing conditions

! If a state requires via ~{ Cond c p }~ that some constraint p is not true, then as soon as it
! becomes known this means that the state can not be consistently assumed
! Couple of possibilities to handle this:
! 1. Use explicit test, keeping the continuations if no answer is known
! 2. Specify an equivalent constraint c2 together with a disjunction c2 ⊕ c , such
!    that if ( <==> c2 p ), where p holds, will cause a { Trivial c2 } constraint
!    to automatically make c absurd
! 3. Do Something similar but using an inverse Cond constraint
!    ~{ Cond p c2 }~

! Trying 2.

CHR: equiv-subsumes-cond @ { Equiv ?c ?p } // { Cond ?c ?p } -- | ;

CHR: disjoint-is-bounded @ { Disjoint { ?c ?c1 } } // { Disjoint { ?c ?c2 } } -- | [ ?c2 ?c1 ==! ] ;
CHR: disjoint-is-bounded @ { Disjoint { ?c1 ?c } } // { Disjoint { ?c ?c2 } } -- | [ ?c2 ?c1 ==! ] ;

CHR: assume-complement-condition @ { Cond ?c P{ Not ?p } } // -- |
{ Equiv ?c2 ?p }
{ Disjoint { ?c2 ?c } } ;

! Is this a recursion problem? For now, there is kind of a "normalization" behavior if we actually
! only ask for one of the conditions in the disjoint set...
CHR: ask-for-complement @ <={ Cond ?c2 ?p } { Disjoint { ?c1 ?c2 } } // -- [ ?p Not? not ] |
{ Cond ?c1 P{ Not ?p } } ;

! eq constraints
CHR: known-test-equal @ { Equiv ?c P{ = A{ ?x } A{ ?y } } } // -- |
[ ?c ?x ?y [ known ] same? [ Trivial boa ] [ Absurd boa ] if ] ;


! Propagate Absurdness
CHR{ { AbsurdState ?s } // { AbsurdState ?s } -- | }
CHR{ { AbsurdScope ?s ?t __ } // { AbsurdScope ?s ?t __ } -- | }

CHR: parent-scope-is-absurd @ { AbsurdState ?t } //
! { Scope ?s ?u __ __ ?l }
<={ Scope ?s ?u __ __ ?l . __ }
--
[ ?t ?l known in? [ t ] [ ?t ?s = ] if ]
| { AbsurdScope ?s ?u ?l } ;

CHR: branches-establish-nesting @ { Branch ?r ?u ?a ?b } // -- | { Necessary ?r ?a } { Necessary ?r ?b } ;

CHR: branches-are-absurd @ { AbsurdState ?s } { Branch ?s ?t ?a ?b } // -- | { AbsurdState ?a } { AbsurdState ?b } ;

! CHR: child-scope-is-absurd @ { AbsurdState ?s } //
CHR: child-scope-is-absurd @ { Absurd ?s } //
! { Scope ?s ?u __ __ ?l }
<={ Scope ?s ?u __ __ ?l . __ }
-- | { AbsurdScope ?s ?u ?l } ;

CHR: absurd-scope-states-are-dead @ { AbsurdScope ?r ?u ?l } // -- [ ?l known? ] | { Dead ?r } { Dead ?u } [ ?l known [ Dead boa ] map ] ;
CHR: absurd-leader-is-cond @ { AbsurdScope ?s __ __ } // -- | { Absurd ?s } ;

! Convert Control Flow

CHR: conflict-state-is-absurd @ // { ConflictState ?t __ __ } -- | { AbsurdState ?t } ;

! Reasoning
CHR: dead-is-unnecessary @ { Dead ?c } // { Necessary __ ?c } -- | ;
! CHR: trivial-is-unneccessary @ { Trivial ?c } // { Necessary __ ?c } -- | ;

CHR: necessary-parts-are-necessary @ { Necessary ?c ?c1 } { Disjoint ?l } // -- [ ?c1 ?l in? ] |
[ ?c ?c1 ?l remove [ Necessary boa ] with map ] ;

! CHR{ { Absurd ?t } // { Cond ?t ?c } -- | }
CHR: kill-absurd-cond-preds @ { Absurd ?s } // <={ cond-pred ?s . __ } -- | ;
! CHR{ { Absurd ?x } // { Disjoint ?x ?y } -- | { Trivial ?y } }
! CHR{ { Absurd ?y } // { Disjoint ?x ?y } -- | { Trivial ?x } }
! CHR{ { Trivial ?x } // { Disjoint ?x ?y } -- | { Absurd ?y } }
! CHR{ { Trivial ?y } // { Disjoint ?x ?y } -- | { Absurd ?x } }
CHR{ { Absurd ?x } // { Disjoint ?l } -- [ ?x known ?l known in? ] | [ ?x known ?l known remove Disjoint boa ] }
! CHR{ { Absurd ?y } { Disjoint ?x ?y } // -- | { Trivial ?x } }
CHR{ { Disjoint { ?x ?y } } // { Trivial ?x } -- | { Absurd ?y } }
CHR{ { Disjoint { ?x ?y } } // { Trivial ?y } -- | { Absurd ?x } }



! Rewrite stuff to branch conditions, to transport that upwards
CHR: propagate-trivial-1 @ { Disjoint { ?c } } { Branch ?r __ ?c __ } // AS: ?x <={ cond-pred ?c . __ } -- |
     [ ?x ?r >>cond ] ;
CHR: propagate-trivial-2 @ { Disjoint { ?c } } { Branch ?r __ __ ?c } // AS: ?x <={ cond-pred ?c . __ } -- |
[ ?x ?r >>cond ] ;

! TODO: maybe that one is the only one needed though?
CHR: propagate-trivial-dep @ { Disjoint { ?c1 } } { Necessary ?c ?c1 } AS: ?x <={ cond-pred ?c1 . __ } // -- |
[ ?x clone ?c >>cond ] ;
;
