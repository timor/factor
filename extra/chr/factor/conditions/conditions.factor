USING: chr chr.factor chr.parser chr.state classes.tuple kernel lists sequences
sets terms ;

IN: chr.factor.conditions

! * Condition system
! - Every Straightline inference has conditions attached to them
! - Any statement about values can be made conditional on that value


! This is left in the compiled constraints, so we can check whether there will
! be a recursive call
TUPLE: cond-pred < chr-pred cond ;
! TUPLE: state-cond < state-pred cond-pred ;
! TUPLE: InlinesUnknown < cond-pred quot ;
! TUPLE: Drop < cond-pred var ;

! Implication
TUPLE: Cond < cond-pred implied ;

TUPLE: Disjoint < chr-pred c1 c2 ;
TUPLE: SameStack < cond-pred s1 s2 ;
TUPLE: Same < cond-pred v1 v2 ;

TUPLE: ConflictState < chr-pred state but why? ;
TUPLE: Absurd < chr-pred cond ;
TUPLE: Trivial < chr-pred cond ;
TUPLE: CondNest < chr-pred c1 c2 ;
TUPLE: AbsurdState < chr-pred state ;
! TUPLE: AbsurdScope < chr-pred beg end ;
TUPLE: AbsurdScope < Scope ;

TUPLE: AcceptType < cond-pred val type ;
TUPLE: ProvideType < cond-pred val type ;

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

CHR: propagate-cond-preds @ { Scope ?s __ ?l } // SUB: ?c cond-pred L{ ?x . ?xs } -- [ ?x ?l in? ] |
    [ ?xs list>array ?s prefix ?c slots>tuple ] ;

! Propagate Absurdness
CHR{ { AbsurdState ?s } // { AbsurdState ?s } -- | }
CHR{ { AbsurdScope ?s ?t __ } // { AbsurdScope ?s ?t __ } -- | }
CHR{ { AbsurdState ?t } // { Scope ?s ?u ?l } -- [ ?t ?l known in? ] | { AbsurdScope ?s ?u ?l } }
CHR{ { AbsurdState ?s } // { Scope ?s ?u ?l } -- | { AbsurdScope ?s ?u ?l } }
CHR{ { AbsurdScope ?r ?u ?l } // { Scope ?s ?t ?v } -- [ ?s ?l in? ] | { AbsurdScope ?s ?t ?l } }
CHR{ { AbsurdScope ?r ?u ?l } // -- [ ?l known? ] | [ ?l known [ AbsurdState boa ] map ] }
! NOTE: this will be needed when we figure out absurdness afterwards
CHR{ { Absurd ?s } { CondJump ?s ?t } // -- | { AbsurdState ?t } }
CHR{ { AbsurdScope ?s __ __ } // -- | { Absurd ?s } }

! Convert Control Flow

! CHR: leader-is-cond-1 @ { CompileRule } { Linkback ?s ?v } // { Cond ?x ?c } -- [ ?x ?v known in? ] | { Cond ?s ?c }  ;
! CHR: leader-is-cond-2 @ { CompileRule } { Linkback ?s ?v } // { CondNest ?x ?y } -- [ ?x ?v known in? ] | { CondNest ?s ?y }  ;

CHR{ // { ConflictState ?t __ __ } -- | { AbsurdState ?t } }

! Reasoning
! CHR{ { Absurd ?t } // { Cond ?t ?c } -- | }
CHR{ { Absurd ?s } // SUB: ?x cond-pred L{ ?s . __ } -- | }
CHR{ { Absurd ?x } // { Disjoint ?x ?y } -- | { Trivial ?y } }
CHR{ { Absurd ?y } // { Disjoint ?x ?y } -- | { Trivial ?x } }

! Value-level handling
CHR{ // { Cond ?c { SameStack L{ ?x . ?xs } L{ ?y . ?ys } } } -- |
     { Cond ?c { Same ?x ?y } }
     { Cond ?c { SameStack ?xs ?ys } } }

! Expand
! CHR{ // { Cond ?c { SameStack ?a L{ ?y . ?ys } } } -- [ ?a known term-var? ] |
!      { Cond ?c { SameStack L{ ?x . ?xs } L{ ?y . ?ys } } } }
! CHR{ // { Cond ?c { SameStack L{ ?x . ?xs } ?b } } -- [ ?b known term-var? ] |
!      { Cond ?c { SameStack L{ ?x . ?xs } L{ ?y . ?ys } } } }
CHR{ { Cond ?c { SameStack ?a L{ ?y . ?ys } } } // -- [ ?a known term-var? ] |
     [ ?a L{ ?x . ?xs } ==! ] }
CHR{ { Cond ?c { SameStack L{ ?x . ?xs } ?b } } // -- [ ?b known term-var? ] |
     [ ?b L{ ?y . ?ys } ==! ] }

! Clean up Links
CHR{ { Absurd ?s } // { CondJump ?s ?t } -- | }
CHR{ { Absurd ?t } // { CondJump ?s ?t } -- | }
! Rewrite stuff to branch conditions, to transport that upwards

CHR: propagate-trivial @ { Trivial ?c } { CondJump ?r ?c } // SUB: ?x cond-pred L{ ?c . ?xs } -- |
     [ ?xs list>array ?r prefix ?x slots>tuple ]
   ;

! NOTE: Assumption, there can only be one jump into ?s
CHR{ // { Trivial ?s } { CondJump ?r ?s } -- | }

;
