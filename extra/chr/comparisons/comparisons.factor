USING: chr chr.factor chr.modular chr.parser chr.state kernel terms ;

IN: chr.comparisons

! * Basic comparison predicates with equality

<PRIVATE
TERM-VARS: ?x ?y ?z ;
PRIVATE>

TUPLE: le < chr-pred x y ;
TUPLE: ge < chr-pred x y ;
TUPLE: lt < chr-pred x y ;
TUPLE: gt < chr-pred x y ;
TUPLE: ne < chr-pred x y ;
TUPLE: is < chr-pred x y ;
TUPLE: eql < chr-pred x y ;
TUPLE: _is < chr-pred x y ;
UNION: comp-pred le ge lt gt ne eql ;
INSTANCE: comp-pred has-opposite
INSTANCE: comp-pred transitive
M: gt opposite-pred drop le ;
M: le opposite-pred drop gt ;
M: ge opposite-pred drop lt ;
M: lt opposite-pred drop ge ;
M: eql opposite-pred drop ne ;
M: ne opposite-pred drop eql ;
CHRAT: chrat-comp { le ge lt gt ne eql is _is }
! CHRAT: chrat-comp { le ge lt gt ne }
    CHR: unique-comp-pred @ AS: ?p <={ comp-pred } // AS: ?q <={ comp-pred } -- [ ?p ?q == ] | ;
    CHR{ // { ne ?x ?x } -- | false }
    CHR{ // { is ?x ?x } -- | }
    CHR{ { is ?x ?y } // { is ?x ?y } -- | }
    CHR{ { is ?x ?y } // { is ?y ?x } -- | }
    ! CHR{ // { is ?x ?y } -- [ ?x ?y [ ground-value? not ] both? ] | [ ?x ?y ==! ] }
    ! CHR{ // { is A{ ?x } A{ ?y } } -- | [ ?x ?y eq? [ f ] [ ?x ?y "inconsistent" throw ] if ] }
    ! CHR{ // { is A{ ?x } A{ ?y } } -- | [ ?x ?y eq? [ f ] [ { Inconsistent P{ is ?x ?y } } ] if ] }
    ! CHR{ // { is A{ ?y } ?x } -- | { is ?x ?y } }
    ! CHR: answer-exist @ { is ?x ?y } // { ask { is ?x ?z } } -- | [ ?z ?y ==! ] { entailed { ask { is ?x ?z } } } ;
    ! CHR: answer-exist @ { is ?x ?y } // { _is ?x ?z } -- | [ ?z ?y ==! ] ;
    ! CHR{ // { ask { is ?x ?y } } -- [ ?x ?y == ] | { entailed { is ?x ?y } } }
    CHR{ { lt ?x ?y } // { ask { ne ?x ?y } } -- | { entailed { ne ?x ?y } } }
    CHR{ // { le ?x ?x } -- | }
    ! CHR{ { le ?x ?y } // { le ?y ?x } -- | [ ?x ?y ==! ] }
    CHR{ { le ?x ?y } // { le ?y ?x } -- | { is ?x ?y } }
    CHR{ { le ?x ?y } { le ?y ?z } // -- | { le ?x ?z } }

    ! CHR{ { le ?x ?y } // { ask { le ?x ?y } } -- | { entailed { le ?x ?y } } }
    CHR{ { lt ?x ?y } // { ask { le ?x ?y } } -- | { entailed { lt ?x ?y } } }

    ! Normalize
    CHR{ // { ge ?x ?y } -- | { le ?y ?x } }

    CHR{ { le ?x ?y } // { ask { ge ?y ?x } } -- | { entailed { ge ?y ?x } } }

    ! CHR{ // { le ?x ?y } { ne ?x ?y } -- | { lt ?x ?y } }

    CHR{ // { lt ?x ?x } -- | false }

    ! Existential guard!
    ! CHR{ { lt ?x ?y } // -- { le ?y ?z } | { lt ?x ?z } }

    ! Express lt with non-equality
    ! CHR: lt-excludes-equality @ { lt ?x ?y } // -- | { ne ?x ?y } ;


    CHR{ { lt ?x ?y } // { lt ?x ?y } -- | }

    ! Normalize
    CHR{ // { gt ?x ?y } -- | { lt ?y ?x } }
;
