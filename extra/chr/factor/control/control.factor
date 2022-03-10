USING: arrays chr chr.comparisons chr.factor chr.factor.conditions chr.modular
chr.parser chr.state kernel math sequences sets splitting terms ;

IN: chr.factor.control

! * Control flow

: insert-after ( new old seq -- seq )
    [ index 1 + ] [ insert-nth ] bi ;

: insert-instead ( new-seq old seq -- seq )
    swap 1array
    split1-slice
    swapd append append ;

TUPLE: Link < chr-pred from to ;
TUPLE: CheckExec < trans-pred word ans ;
TUPLE: RecursiveCall < trans-pred word back-to ;
TUPLE: AddLink < trans-pred ;
TUPLE: PrefixLink < trans-pred ;
TUPLE: ScopeLeader < chr-pred state leader ;
TUPLE: Jump < chr-pred from to ;

CHRAT: control-flow { CheckExec }

! CHR{ { AbsurdState ?s } // { AddLink ?s __ } -- | }

CHR{ { Link ?t ?u } // { Link ?t ?u } -- | }

! Returning answer
! CHR{ { Entry ?r ?w } // { Link ?r ?s } { CheckExec ?s ?t ?w } --
!      | { RecursiveCall ?s ?t ?w ?r } }
CHR: answer-check-exec-recursive @ { Entry ?r ?w } // { Link ?r ?s } { ask { CheckExec ?s ?t ?w ?x } } --
| [ ?x ?r ==! ] { entailed { CheckExec ?s ?t ?w ?x } } ;

CHR: answer-check-exec-normal @ // { Link +top+ ?s } { ask { CheckExec ?s ?t ?w ?x } } --
| [ ?x f ==! ] { entailed { CheckExec ?s ?t ?w ?x } } ;
! CHR{ // { Link +top+ ?s } { CheckExec ?s ?t ?w } --
!      | { ExecWord ?s ?t ?w } }

! Initiating Query
CHR{ { ask { CheckExec ?t __ __ __ } } // -- | { Link ?t ?t } }

! ! Adding elements
! CHR: add-link-to-scope-leader @ // { Scope ?s ?u ?a } { AddLink ?s ?t } -- |
!    [ ?s ?u ?a ?t suffix Scope boa ] ;

! CHR: add-link-to-scope-member @ // { Scope ?s ?u ?a } { AddLink ?t ?b } -- [ ?t ?a known in? ] |
!      [| |
!       ?b ?t ?a insert-after :> a2
!       { Scope ?s ?u a2 }
!      ] ;

! ! In case we cannot be added to an existing scope, we might actually be leading it
! CHR: lead-scope @ // { Scope ?s ?t ?l } { PrefixLink ?r ?s } -- [ ?l known? ] |
!     [ ?r ?t ?l ?s prefix Scope boa ] ;

! CHR{ { Linkback ?r ?a } // { Linkback ?r ?b } -- [ ?b ?a subset? ] | }
! CHR{ // { Linkback ?r ?a } { Linkback ?r ?b } -- | [| | ?a ?b union :> c { Linkback ?r c } ] }

! Propagation
! CHR{ { Scope ?s __ ?l } // { Link ?t ?u } -- [ ?s ?t == not ] [ ?t ?l in? ] | { Link ?s ?u } }
CHR{ <={ Scope ?s __ __ __ ?l . __ }  // { Link ?t ?u } -- [ ?s ?t == not ] [ ?t ?l in? ] | { Link ?s ?u } }

! CHR{ // { Scope ?r ?u ?l } { Scope ?s __ ?a } -- [ ?s ?l in? ] |
!      [ ?r ?u ?a ?s ?l insert-instead Scope boa ]
!    }

CHR: cond-state-link @ { --> __ P{ is ?s ?r } } // { Link ?r ?u } -- | { Link ?s ?u } ;

CHR{ { Branch ?s __ ?r __ } // { Link ?r ?u } -- | { Link ?s ?u } }
CHR{ { Branch ?s __ __ ?r } // { Link ?r ?u } -- | { Link ?s ?u } }
CHR{ { Jump ?s ?r } // { Link ?r ?u } -- | { Link ?s ?u } }

! Transitivity?
! CHR{ // { Link ?r ?s } { Link ?s ?t } -- | { Link ?r ?t } }

! Any trans-pred is by default a control path link
CHR: trans-check-exec @ <={ trans-pred ?s ?r . __ } // { Link ?r ?u } -- |
{ Link ?s ?u } ;

    ;
