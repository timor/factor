USING: accessors chr chr.factor chr.parser chr.state combinators.short-circuit
kernel lists math sequences sets terms types.util ;

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

! Implication
TUPLE: Cond < cond-pred implied ;

TUPLE: Equiv < chr-pred c1 c2 ;

TUPLE: Disjoint < chr-pred c1 c2 ;
TUPLE: SameStack < chr-pred s1 s2 ;
TUPLE: Same < chr-pred v1 v2 ;

TUPLE: ConflictState < chr-pred state but why? ;
TUPLE: Absurd < chr-pred cond ;
TUPLE: Trivial < chr-pred cond ;
TUPLE: CondNest < chr-pred c1 c2 ;
TUPLE: AbsurdState < chr-pred state ;
TUPLE: AbsurdScope < chr-pred beg end states ;
! TUPLE: AbsurdScope < Scope ;

! TODO move
TUPLE: AcceptType < state-pred val type ;
TUPLE: ProvideType < state-pred val type ;

CHRAT: condition-prop {  }

! Redundancies
CHR{ { Absurd ?x } // { Absurd ?x } -- | }

CHR{ // { CondNest ?x ?x } -- | }
CHR{ { Cond ?x ?c } // { Cond ?x ?c } -- | }

! Conditional jump scope entries are the conditions!
! CHR: leader-is-cond-1 @ { CompileRule } { Linkback ?s ?v } // { Cond ?x ?c } -- [ ?x ?v known in? ] | { Cond ?s ?c }  ;

! Rewrite stuff to scope leaders
! CHR{ { Scope ?s __ ?l } // { Cond ?t ?k } -- [ ?t ?l known in? ] | { Cond ?s ?k } }
! CHR{ { Scope ?s __ ?l } // { Absurd ?t } -- [ ?t ?l known in? ] | { Absurd ?s } }
! CHR{ { Scope ?s __ ?l } // { Trivial ?t } -- [ ?t ?l known in? ] | { Trivial ?s } }

! CHR: propagate-cond-preds @ { Scope ?s __ ?l } // SUB: ?c cond-pred L{ ?x . ?xs } -- [ ?x ?l in? ] |
!     [ ?xs list>array ?s prefix ?c slots>tuple ] ;
CHR: propagate-cond-preds-scope @ { Scope ?s __ __ __ ?l } // SUB: ?c cond-pred L{ ?x . __ } -- [ ?x ?l in? ] |
    [ ?c ?s >>cond ] ;

CHR: propagate-cond-preds-trans @ SUB: ?x trans-pred L{ ?r ?s . __ } // SUB: ?c cond-pred L{ ?s . __ } -- |
[ ?c ?r >>cond ] ;


! Propagate Absurdness
CHR{ { AbsurdState ?s } // { AbsurdState ?s } -- | }
CHR{ { AbsurdScope ?s ?t __ } // { AbsurdScope ?s ?t __ } -- | }

CHR: parent-scope-is-absurd @ { AbsurdState ?t } //
! { Scope ?s ?u __ __ ?l }
SUB: ?x Scope L{ ?s ?u __ __ ?l . __ }
-- [ ?t ?l known in? ] | { AbsurdScope ?s ?u ?l } ;

CHR: child-scope-is-absurd @ { AbsurdState ?s } //
! { Scope ?s ?u __ __ ?l }
SUB: ?x Scope L{ ?s ?u __ __ ?l . __ }
-- | { AbsurdScope ?s ?u ?l } ;

! CHR: subscopes-are-absurd @ { AbsurdScope ?r ?u ?l } //
! ! { Scope ?s ?t __ __ ?v }
! SUB: ?x Scope L{ ?s ?u __ __ ?l . __ }
! -- [ ?s ?l in? ] | { AbsurdScope ?s ?t ?l } ;

CHR: scope-states-are-absurd @ { AbsurdScope ?r ?u ?l } // -- [ ?l known? ] | { AbsurdState ?r } { AbsurdState ?u } [ ?l known [ AbsurdState boa ] map ] ;
! NOTE: this will be needed when we figure out absurdness afterwards
CHR: implied-cond-jump-is-absurd @ { Absurd ?s } { CondJump ?s ?t } // -- | { AbsurdState ?t } ;
CHR: absurd-leader-is-cond @ { AbsurdScope ?s __ __ } // -- | { Absurd ?s } ;

! Convert Control Flow

! CHR: leader-is-cond-1 @ { CompileRule } { Linkback ?s ?v } // { Cond ?x ?c } -- [ ?x ?v known in? ] | { Cond ?s ?c }  ;
! CHR: leader-is-cond-2 @ { CompileRule } { Linkback ?s ?v } // { CondNest ?x ?y } -- [ ?x ?v known in? ] | { CondNest ?s ?y }  ;

CHR: conflict-state-is-absurd @ // { ConflictState ?t __ __ } -- | { AbsurdState ?t } ;

! Reasoning
! CHR{ { Absurd ?t } // { Cond ?t ?c } -- | }
CHR: kill-absurd-cond-preds @ { Absurd ?s } // SUB: ?x cond-pred L{ ?s . __ } -- | ;
CHR{ { Absurd ?x } // { Disjoint ?x ?y } -- | { Trivial ?y } }
CHR{ { Absurd ?y } // { Disjoint ?x ?y } -- | { Trivial ?x } }

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
SUB: ?x cond-pred L{ ?c1 . ?a }
SUB: ?y cond-pred L{ ?c2 . ?a } -- |
! [ ?x clone ?r >>cond ] ;
[ ?x ?r >>cond ] ;


! Rewrite stuff to branch conditions, to transport that upwards
! CHR: propagate-trivial @ { Trivial ?c } { CondJump ?r ?c } // SUB: ?x cond-pred L{ ?c . ?xs } -- |
CHR: propagate-trivial @ { Trivial ?c } { CondJump ?r ?c } // SUB: ?x cond-pred L{ ?c . __ } -- |
     ! [ ?xs list>array ?r prefix ?x slots>tuple ]
     [ ?x ?r >>cond ]
   ;

! Clean up jump artifacts
CHR: absurd-jump-from @ { Absurd ?r } // { CondJump ?r __ } -- | ;
! CHR: absurd-ret-from @ { Absurd ?u } // { CondRet __ ?u } -- | ;
CHR: absurd-jump-to @ { Absurd ?s } // { CondJump __ ?s } -- | ;
! CHR: absurd-ret-to @ { Absurd ?t } // { CondRet ?t __ } -- | ;


! NOTE: Assumption, there can only be one jump into ?s
! CHR{ // { Trivial ?s } { CondJump ?r ?s } -- | }

;
