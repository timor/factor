USING: chr chr.modular chr.parser chr.state kernel linked-assocs make math
tools.test ;
IN: chr.modular.tests

TUPLE: leq < chr-pred v1 v2 ;

! SYMBOLS: A B C ;
TERM-VARS: A B C ;


TERM-VARS: ?x ?y ?z ;

TUPLE: eq < chr-pred v1 v2 ;
! Equality solver from schrijvers paper
TERM-VARS: ?x1 ?y1 ?x2 ?y2 ;
CONSTANT: eq-solver {
CHR: reflexive @ // { eq ?x ?y } -- [ ?x ?y == ] | ;
CHR: redundant @ { eq ?x1 ?y1 } // { eq ?x2 ?y2 } -- [ ?x1 ?x2 == ] [ ?y1 ?y2 == ] | ;
CHR: symmetric @ { eq ?x ?y } // -- | { eq ?y ?x } ;
CHR: transitive @ { eq ?x1 ?y1 } { eq ?x2 ?y2 } // -- [ ?y1 ?x2 == ] | { eq ?x1 ?y2 } ;
}


{
    LH{ { 1 P{ eq A B } }
        { 2 P{ eq B A } }
        { 6 P{ eq B C } }
        { 7 P{ eq C B } }
        { 10 P{ eq C A } }
        { 11 P{ eq A C } } }
}
[ eq-solver { { eq A B } { eq B C } } run-chr-query ] unit-test


! This is the original example, relying on builtin equality solver
! This needs an implementation of asking for syntactic equality, but gives the
! exact same trace as the chrat one
CONSTANT: leq-solver-orig {
    CHR: reflexivity @ // { leq ?x ?y } -- [ ?x ?y == ] | ;
CHR: antisymmetry @ // { leq ?x ?y } { leq ?y ?x } -- | [ ?x ?y ==! ] ;
CHR: transitivity @ { leq ?x ?y } { leq ?y ?z } // -- | { leq ?x ?z } ;
}

{
    LH{ { 5 { = C A } } { 6 { = C B } } }
}
[ leq-solver-orig { { leq A B } { leq C A } { leq B C } } run-chr-query ] unit-test

{
   { f }
}
[
    [
        leq-solver-orig
        { { leq A B } { leq C A } { leq B C } [ A 42 == [ t , ] [ f , ] if f ] } run-chr-query drop
    ] {  } make
] unit-test

{
    { t }
}
[
    [
        leq-solver-orig
        { { leq A B } { leq C A } { leq B C } [ A B == [ t , ] [ f , ] if f ] } run-chr-query drop
    ] {  } make
] unit-test

TERM-VARS: ?k ;
! This is the example from the CHRat paper
! rule-name @ Hk... \ Hr... <=> G.. | B ;
! CHR{ Hk.. // Hr.. -- G.. | B }
CONSTANT: leq-solver-chrat {
    CHR{ // { leq ?x ?x } -- | }
    CHR{ // { leq ?x ?y } { leq ?y ?x } -- | [ ?x ?y ==! ] }
    CHR{ { leq ?x ?y } { leq ?y ?z } // -- | { leq ?x ?z } }
    CHR{ { leq ?x ?y } // { leq ?x ?y } -- | }

    ! Entailment
    CHR{ { leq ?x ?y } // { ask { leq ?x ?y } ?k } -- | { entailed ?k } }
    ! Reflexive case handled specially, not entirely sure what the formal
    ! reasoning is behind that...
    CHR{ // { ask { leq ?x ?x } ?k } -- | { entailed ?k } }
    ! This is a shortcut to the underlying host:
    CHR{ // { ask { leq ?x ?y } ?k } -- [ ?x ?y <= ] | { entailed ?k } }
}

{
    LH{ { 5 { = C A } } { 6 { = C B } } }
}
[ leq-solver-chrat { { leq A B } { leq C A } { leq B C } } run-chr-query ] unit-test

{ { f } }
[
    [
        leq-solver-chrat
        { { leq A B } { leq C A } { leq B C } [ A 42 == [ t , ] [ f , ] if f ] } run-chr-query drop
    ] {  } make
] unit-test

SYMBOL: D

{ { f } }
[
    [
        leq-solver-chrat
        { { leq A B } { leq C A } { leq B C } [ A D == [ t , ] [ f , ] if f ] } run-chr-query drop
    ] {  } make
] unit-test

{ { t } }
[
    [
        leq-solver-chrat
        { { leq A B } { leq C A } { leq B C } [ A B == [ t , ] [ f , ] if f ] } run-chr-query drop
    ] {  } make
] unit-test
! CHRat paper example
! component min_solver .
! import leq /2 from leq_solver .
! export min /3.
! min(X, Y, Z) <=> leq(X, Y) | Z = X .
! min(X, Y, Z) <=> leq(Y, X) | Z = Y .
! min(X, Y, Z) ==> leq(Z, X), leq(Z, Y).
!
! min(X, Y, Z) \ ask(min(X, Y, Z), K) <=> entailed(K).
! ask(min(X, Y, X), K) <=> leq(X, Y) | entailed(K).
! ask(min(X, Y, Y), K) <=> leq(Y, X) | entailed(K).


TUPLE: some < chr-pred arg ;
! Manually transformed example
TUPLE: min < chr-pred a b c ;
SYMBOLS: r1 r2 r3 r4 ;
TERM-VARS: ?k0 ;
CONSTANT: chrat-min {
    CHR{ { min ?x ?y ?z } // { ask { min ?x ?y ?z } ?k } -- | { entailed ?k } }

    CHR{ { min ?x ?y ?z } // -- | gen{ ?k | { ask { leq ?x ?y } ?k } { some { r1 ?x ?y ?z ?k } } } }
    CHR{ // { some { r1 ?x ?y ?z ?k } } { min ?x ?y ?z } { entailed ?k } -- | [ ?z ?x ==! ] }

    CHR{ { min ?x ?y ?z } // -- | gen{ ?k | { ask { leq ?y ?x } ?k } { some { r2 ?x ?y ?z ?k } } } }
    CHR{ // { some { r2 ?x ?y ?z ?k } } { min ?x ?y ?z } { entailed ?k } -- | [ ?z ?y ==! ] }

    CHR{ { min ?x ?y ?z } // -- | { leq ?z ?x } { leq ?z ?y } }

    ! NOTE: do we need to instantiate k0 here? If we never modify the internal store, call-stack semantics should prohibit invalid substitutions, no?
    CHR{ { ask { min ?x ?y ?x } ?k } // -- | gen{ ?k0 | { ask { leq ?x ?y } ?k0 } { some { r3 ?x ?y ?k ?k0 } } } }
    CHR{ // { some { r3 ?x ?y ?k ?k0 } } { ask { min ?x ?y ?x } ?k } { entailed ?k0 } -- | { entailed { min ?x ?y ?x } } { entailed ?k } }

    CHR{ { ask { min ?x ?y ?y } ?k } // -- | gen{ ?k0 | { ask { leq ?y ?x } ?k0 } { some { r4 ?x ?y ?k ?k0 } } } }
    CHR{ // { some { r4 ?x ?y ?k ?k0 } } { ask { min ?x ?y ?y } ?k } { entailed ?k0 } -- | { entailed { min ?x ?y ?y } } { entailed ?k } }
}
