USING: chr.factor chr.factor.quotations chr.parser chr.state kernel math
sequences sequences.extras sets terms ;

IN: chr.factor.control

! * Control flow

: insert-after ( new old seq -- seq )
    [ index 1 + ] [ insert-nth ] bi ;

TERM-VARS: ?t ?u ?r ?w ?s ?a ?l ?b ?v ;

CHRAT: control-flow { CheckExec AddLink }

CHR{ { Link ?t ?u } // { Link ?t ?u } -- | }

! Returning answer
CHR{ { Entry ?r ?w } // { Link ?r ?s } { CheckExec ?s ?t ?w } --
     | { RecursiveCall ?s ?t ?w ?r } }

CHR{ // { Link +top+ ?s } { CheckExec ?s ?t ?w } --
     | { ExecWord ?s ?t ?w } }

! Initiating Query
CHR{ { CheckExec ?t __ __ } // -- | { Link ?t ?t } }

! Adding elements
CHR{ // { Scope ?s ?u ?a } { AddLink ?s ?t } -- |
   [ ?s ?u ?a ?t suffix Scope boa ] }

CHR{ // { Scope ?s ?u ?a } { AddLink ?t ?b } -- [ ?t ?a known in? ] |
     [| |
      ?b ?t ?a insert-after :> a2
      { Scope ?s ?u a2 }
     ] }

! CHR{ { Linkback ?r ?a } // { Linkback ?r ?b } -- [ ?b ?a subset? ] | }
! CHR{ // { Linkback ?r ?a } { Linkback ?r ?b } -- | [| | ?a ?b union :> c { Linkback ?r c } ] }

! Propagation
CHR{ { Scope ?s __ ?l } // { Link ?t ?u } -- [ ?s ?t == not ] [ ?t ?l in? ] | { Link ?s ?u } }

CHR{ { CondJump ?s ?r __ } // { Link ?r ?u } -- | { Link ?s ?u } }


! Transitivity?
! CHR{ // { Link ?r ?s } { Link ?s ?t } -- | { Link ?r ?t } }

;
