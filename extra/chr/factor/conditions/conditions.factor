USING: accessors assocs chr chr.factor chr.modular chr.parser chr.state kernel
lists math namespaces sequences sets terms ;

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
! TUPLE: Requires < cond-pred consequence ;

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
CHR{ AS: ?p <={ cond-pred ?s } // AS: ?q <={ cond-pred ?s } -- [ ?p ?q [ class-of ] same? ] | }

! Reverse dependencies to scopes
! CHR: analyze-state-constraint @ // { StateConstraint ?s ?x } -- |

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
CHR: assume-complement-condition @ // { Cond ?c P{ Not ?p } } -- |
{ Equiv ?c2 ?p }
{ Disjoint ?c ?c2 } ;


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

CHR: branches-are-absurd @ { AbsurdState ?s } { Branch ?s ?t ?a ?b } // -- | { AbsurdState ?a } { AbsurdState ?b } ;

! CHR: child-scope-is-absurd @ { AbsurdState ?s } //
CHR: child-scope-is-absurd @ { Absurd ?s } //
! { Scope ?s ?u __ __ ?l }
<={ Scope ?s ?u __ __ ?l . __ }
-- | { AbsurdScope ?s ?u ?l } ;

! CHR: subscopes-are-absurd @ { AbsurdScope ?r ?u ?l } //
! ! { Scope ?s ?t __ __ ?v }
! SUB: ?x Scope L{ ?s ?u __ __ ?l . __ }
! -- [ ?s ?l in? ] | { AbsurdScope ?s ?t ?l } ;

CHR: absurd-scope-states-are-dead @ { AbsurdScope ?r ?u ?l } // -- [ ?l known? ] | { Dead ?r } { Dead ?u } [ ?l known [ Dead boa ] map ] ;
CHR: absurd-leader-is-cond @ { AbsurdScope ?s __ __ } // -- | { Absurd ?s } ;

! Convert Control Flow

! CHR: leader-is-cond-1 @ { CompileRule } { Linkback ?s ?v } // { Cond ?x ?c } -- [ ?x ?v known in? ] | { Cond ?s ?c }  ;
! CHR: leader-is-cond-2 @ { CompileRule } { Linkback ?s ?v } // { CondNest ?x ?y } -- [ ?x ?v known in? ] | { CondNest ?s ?y }  ;

CHR: conflict-state-is-absurd @ // { ConflictState ?t __ __ } -- | { AbsurdState ?t } ;

! Reasoning
! CHR{ { Absurd ?t } // { Cond ?t ?c } -- | }
CHR: kill-absurd-cond-preds @ { Absurd ?s } // <={ cond-pred ?s . __ } -- | ;
CHR{ { Absurd ?x } // { Disjoint ?x ?y } -- | { Trivial ?y } }
CHR{ { Absurd ?y } // { Disjoint ?x ?y } -- | { Trivial ?x } }
CHR{ { Trivial ?x } // { Disjoint ?x ?y } -- | { Absurd ?y } }
CHR{ { Trivial ?y } // { Disjoint ?x ?y } -- | { Absurd ?x } }
! CHR{ // { Trivial ?x } { Disjoint ?x ?y } -- | { Absurd ?y } }
! CHR{ // { Trivial ?y } { Disjoint ?x ?y } -- | { Absurd ?x } }

! Balanced stacks through branches

: list>simple-type ( list1 -- n last )
    0 swap [ dup atom? ] [ [ 1 + ] dip cdr ] until ; inline

: ?effect-height ( list1 list2 -- n/f )
    [ list>simple-type ] bi@ swapd
    = [ - ] [ 2drop f ] if ;

! ERROR: imbalanced-branch-stacks i1 o1 i2 o2 ;

! CHR: require-balanced-branch-stacks @ { Branch ?r ?c1 ?c2 }
! ! { Cond ?c1 P{ SameStack ?rho ?a } }
! ! { Cond ?c1 P{ SameStack ?x ?sig } }
! ! { Cond ?c2 P{ SameStack ?rho ?b } }
! ! { Cond ?c2 P{ SameStack ?y ?sig } } // -- [ break ?a known llength* ?b known llength* = dup [ "branch imbalance" throw ] unless ] | [ ?x ?y ==! ] ;
! { Cond ?c1 P{ SameStack ?rho ?a } }
! { Cond ?c1 P{ SameStack ?x ?sig } }
! { Cond ?c2 P{ SameStack ?rho ?b } }
! { Cond ?c2 P{ SameStack ?y ?sig } }
! // --
! [ ?a ?x ?effect-height :>> ?v ] [ ?b ?y ?effect-height :>> ?w ]
! |
! [
!     ?v ?w { [ and ] [ = not ] } 2&&
!     [ ?a ?x ?b ?y imbalanced-branch-stacks ] when

!     ?rho lastcdr ?sig lastcdr ==!
! ]
! ! [ ?x ?y ==! ]
!     ;

! Value-level handling

! Expand
! This is tricky.  New strategy: in one direction we set it to equal, in the other, we generate new vars?
CHR: assume-stack-left @ { Cond ?c P{ SameStack ?a L{ ?y . ?ys } } } // -- [ ?a known term-var? ] |
[ ?a L{ ?x . ?xs } ==! ] ;
CHR: assume-stack-right @ { Cond ?c P{ SameStack L{ ?x . ?xs } ?b } } // -- [ ?b known term-var? ] |
[ ?b L{ ?y . ?ys } ==! ] ;
! CHR: assume-stack-right @ // { Cond ?c P{ SameStack L{ ?x . ?xs } ?b } } -- [ ?b known term-var? ] |
! { Cond ?c P{ SameStack L{ ?x . ?xs } L{ ?y . ?b } } } ;
! [ ?b L{ ?y . ?ys } ==! ] ;

CHR: same-stack-tos @ { Cond ?c P{ SameStack L{ ?x . ?xs } L{ ?y . ?ys } } } // -- |
{ Cond ?c P{ Same ?x ?y } }
{ Cond ?c P{ Same ?xs ?ys } } ;

CHR: destruct-same-stack-values @ // { Cond ?c P{ Same L{ ?x . ?xs } L{ ?y . ?ys } } } -- |
     { Cond ?c P{ Same ?x ?y } }
     ! { Cond ?c P{ SameStack ?xs ?ys } }
     { Cond ?c P{ Same ?xs ?ys } }
    ;






! If Conjunctions are true in both branches, they are true in parent scope
CHR: propagate-disjoint-tautology @
{ CondJump ?r ?c1 } { CondJump ?r ?c2 } { Disjoint ?c1 ?c2 } //
AS: ?x <={ cond-pred ?c1 . ?a }
<={ cond-pred ?c2 . ?a } -- |
! [ ?x clone ?r >>cond ] ;
[ ?x ?r >>cond ] ;


! Rewrite stuff to branch conditions, to transport that upwards
! CHR: propagate-trivial @ { Trivial ?c } { CondJump ?r ?c } // SUB: ?x cond-pred L{ ?c . ?xs } -- |
CHR: propagate-trivial-1 @ { Trivial ?c } { Branch ?r __ ?c __ } // AS: ?x <={ cond-pred ?c . __ } -- |
     [ ?x ?r >>cond ] ;
CHR: propagate-trivial-2 @ { Trivial ?c } { Branch ?r __ __ ?c } // AS: ?x <={ cond-pred ?c . __ } -- |
[ ?x ?r >>cond ] ;

! Clean up jump artifacts
CHR: absurd-jump-from @ { Absurd ?r } // { CondJump ?r __ } -- | ;
! CHR: absurd-ret-from @ { Absurd ?u } // { CondRet __ ?u } -- | ;
CHR: absurd-jump-to @ { Absurd ?s } // { CondJump __ ?s } -- | ;
! CHR: absurd-ret-to @ { Absurd ?t } // { CondRet ?t __ } -- | ;


! NOTE: Assumption, there can only be one jump into ?s
! CHR{ // { Trivial ?s } { CondJump ?r ?s } -- | }

;
