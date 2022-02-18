USING: chr chr.factor chr.parser chr.state classes.tuple kernel sequences sets
terms ;

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

TUPLE: Disjoint < chr-pred cond1 cond2 ;

TUPLE: ConflictState < cond-pred but why? ;
TUPLE: Absurd < chr-pred cond ;
TUPLE: Trivial < chr-pred cond ;
TUPLE: CondNest < chr-pred c1 c2 ;

TERM-VARS: ?r ?s ?t ?u ?a ?b ?c ?x ?y ?l ?k ?tau ;

CHRAT: condition-prop {  }

! Redundancies
CHR{ { Absurd ?x } // { Absurd ?x } -- | }

CHR{ // { CondNest ?x ?x } -- | }
CHR{ { Cond ?x ?c } // { Cond ?x ?c } -- | }

! Conditional jump scope entries are the conditions!
! CHR: leader-is-cond-1 @ { CompileRule } { Linkback ?s ?v } // { Cond ?x ?c } -- [ ?x ?v known in? ] | { Cond ?s ?c }  ;

! Rewrite stuff to scope leaders
CHR{ { Scope ?s __ ?l } // { Cond ?t ?k } -- [ ?t ?l known in? ] | { Cond ?s ?k } }


! Convert Control Flow

! CHR: leader-is-cond-1 @ { CompileRule } { Linkback ?s ?v } // { Cond ?x ?c } -- [ ?x ?v known in? ] | { Cond ?s ?c }  ;
! CHR: leader-is-cond-2 @ { CompileRule } { Linkback ?s ?v } // { CondNest ?x ?y } -- [ ?x ?v known in? ] | { CondNest ?s ?y }  ;

! Reasoning
CHR{ { Absurd ?t } // { Cond ?t ?c } -- | }
CHR{ { Absurd ?x } // { Disjoint ?x ?y } -- | { Trivial ?y } }
CHR{ { Absurd ?y } // { Disjoint ?x ?y } -- | { Trivial ?x } }
CHR{ // { ConflictState ?t __ __ } -- | { Absurd ?t } }

! Rewrite stuff to branch conditions, to transport that upwards
! FIXME: make this general somehow
! CHR{ { CondJump ?r ?s } // { Cond ?r ?k } -- | { Cond ?c ?k } }

CHR{ // { ConflictState ?t ?c ?k } -- [ ?t +top+? not ] | { Cond ?t { ConflictState ?c ?k } } }
CHR{ // { Drop ?t ?x } -- [ ?t +top+? not ] | { Cond ?t { Drop ?x } } }
CHR{ // { Dup ?t ?x ?y } -- [ ?t +top+? not ] | { Cond ?t { Dup ?x ?y } } }

! Don't keep literal-related stuff
CHR{ // { Cond __ { Drop ?x } } -- | { Dead ?x } }

! Put stuff back
CHR{ // { Cond +top+ ?a } -- [ ?a sequence? ] [ ?a ?first { ConflictState Drop } in? ] |
     [| | ?a unclip :> ( args pred )
       args +top+ prefix pred slots>tuple
     ]
   }

;
