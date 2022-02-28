USING: accessors chr chr.factor chr.parser chr.state classes kernel sequences
sets terms ;

IN: chr.factor.conditions

! * Condition system
! - Every Straightline inference has conditions attached to them
! - Any statement about values can be made conditional on that value


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

TUPLE: Disjoint < chr-pred c1 c2 ;
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

! This couples a condition to a state, So that if the state is unreachable, the
! assumptions can be deleted.

! Destructure to make sure relevance is coupled
TUPLE: StateConstraint < chr-pred state constraint ;
! Capture Relevance
TUPLE: ScopeConds < cond-pred conds ;

! TODO move
TUPLE: AcceptType < state-pred val type ;
TUPLE: ProvideType < state-pred val type ;

CHRAT: condition-prop { Not }

! NOTE: Potentially very expensive?
! CHR: presence-is-trivial @ // { CheckTrivial ?c } --
! [ store get [ nip constraint>> ?c = ] assoc-any? ] |
! { IsTrivial ?c } ;

! Redundancies
CHR{ { Absurd ?x } // { Absurd ?x } -- | }

CHR{ // { CondNest ?x ?x } -- | }
! CHR{ { Cond ?x ?c } // { Cond ?x ?c } -- | }
! CHR{ AS: ?p <={ cond-pred ?s } // AS: ?q <={ cond-pred ?s } -- [ ?p ?q [ class-of ] same? ] | }
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
// AS: ?c <={ cond-pred ?s . __ } -- [ ?s ?l known in? ] |
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

CHR: complement-known @ { Cond ?c ?p } { Not ?p } // -- | { Absurd ?c } ;

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

CHR: disjoint-is-bounded @ { Disjoint ?c ?c1 } // { Disjoint ?c ?c2 } -- | [ ?c2 ?c1 ==! ] ;
CHR: disjoint-is-bounded @ { Disjoint ?c1 ?c } // { Disjoint ?c ?c2 } -- | [ ?c2 ?c1 ==! ] ;

CHR: assume-complement-condition @ // { Cond ?c P{ Not ?p } } -- |
{ Equiv ?c2 ?p }
{ Disjoint ?c ?c2 } ;

! Is this a recursion problem?
CHR: ask-for-complement @ { Cond ?c1 ?p } { Disjoint ?c1 ?c2 } // -- |
{ Cond ?c2 P{ Not ?p } } ;


! Test for triviality of complement once
! CHR: ask-trivial-contradiction @ { Cond ?c ?p } //
! -- { IsTrivial P{ Not ?p } ?b } |
! { IsTrivial P{ Not ?p } ?b } ;



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
CHR: trivial-is-unneccessary @ { Trivial ?c } // { Necessary __ ?c } -- | ;

! CHR{ { Absurd ?t } // { Cond ?t ?c } -- | }
CHR: kill-absurd-cond-preds @ { Absurd ?s } // <={ cond-pred ?s . __ } -- | ;
CHR{ { Absurd ?x } // { Disjoint ?x ?y } -- | { Trivial ?y } }
CHR{ { Absurd ?y } // { Disjoint ?x ?y } -- | { Trivial ?x } }
CHR{ { Trivial ?x } // { Disjoint ?x ?y } -- | { Absurd ?y } }
CHR{ { Trivial ?y } // { Disjoint ?x ?y } -- | { Absurd ?x } }
! CHR{ // { Trivial ?x } { Disjoint ?x ?y } -- | { Absurd ?y } }
! CHR{ // { Trivial ?y } { Disjoint ?x ?y } -- | { Absurd ?x } }



! Rewrite stuff to branch conditions, to transport that upwards
CHR: propagate-trivial-1 @ { Trivial ?c } { Branch ?r __ ?c __ } // AS: ?x <={ cond-pred ?c . __ } -- |
     [ ?x ?r >>cond ] ;
CHR: propagate-trivial-2 @ { Trivial ?c } { Branch ?r __ __ ?c } // AS: ?x <={ cond-pred ?c . __ } -- |
[ ?x ?r >>cond ] ;


;
