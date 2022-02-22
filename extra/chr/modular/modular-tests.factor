USING: accessors arrays assocs chr chr.factor chr.modular chr.parser chr.state
combinators.short-circuit grouping hashtables kernel linked-assocs
macros.expander make math quotations sequences sets terms tools.test words ;
IN: chr.modular.tests

TUPLE: leq < chr-pred v1 v2 ;

: >old-builtins ( result -- result )
    builtins over [ [ [ lhs>> ] [ rhs>> ] bi \ = -rot 3array ] map ] change-at ;


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
    LH{
        { builtins V{ } }
        { 1 P{ eq A B } }
        { 2 P{ eq B A } }
        { 5 P{ eq B C } }
        { 6 P{ eq C B } }
        { 9 P{ eq C A } }
        { 10 P{ eq A C } } }
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
    LH{ { builtins V{ { = C B } { = C A } } } }
}
[ leq-solver-orig { { leq A B } { leq C A } { leq B C } } run-chr-query >old-builtins ] unit-test

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
CHRAT: leq-solver-chrat { leq }
    CHR{ // { leq ?x ?x } -- | }
    CHR{ // { leq ?x ?y } { leq ?y ?x } -- | [ ?x ?y ==! ] }
    CHR{ { leq ?x ?y } { leq ?y ?z } // -- | { leq ?x ?z } }
    CHR{ { leq ?x ?y } // { leq ?x ?y } -- | }

    ! ! Entailment
    ! Reflexive case handled specially, not entirely sure what the formal
    ! reasoning is behind that...
    CHR{ // { ask { leq ?x ?x } } -- | { entailed { leq ?x ?x } } }
    ! This is a shortcut to the underlying host:
    ! If we can prove the opposite, return that!
    CHR{ // { ask { leq ?x ?y } } -- [ ?x ?y <= ] | { entailed { leq ?x ?y } } }
;

{
    LH{ { builtins V{ { = C B } { = C A } } } }
}
[ leq-solver-chrat { { leq A B } { leq C A } { leq B C } } run-chr-query >old-builtins ] unit-test

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


TUPLE: min < chr-pred a b c ;
! SYMBOLS: r1 r2 r3 r4 r5 r6 r7 ;
! TERM-VARS: ?k0 ?m ;
! CONSTANT: chrat-min {
CHRAT: chrat-min { min }
    CHR{ { min ?x ?y ?z } // { ask { min ?x ?y ?z } } -- | { entailed { min ?x ?y ?z } } }

    CHR{ // { min ?x ?y ?z } -- { leq ?x ?y } | [ ?z ?x ==! ] }
    ! NOTE: the second constraint makes sure the continuation is linked to the initial query, but that could have been done with the

    CHR{ // { min ?x ?y ?z } -- { leq ?y ?x } | [ ?z ?y ==! ] }

    CHR{ { min ?x ?y ?z } // -- | { leq ?z ?x } { leq ?z ?y } }

    CHR{ // { ask { min ?x ?y ?x } } -- { leq ?x ?y } | { entailed { min ?x ?y ?y } } }

    CHR{ // { ask { min ?x ?y ?y } } -- { leq ?y ?x } | { entailed { min ?x ?y ?y } } }
;

TERM-VARS: X Y Z M ;
: combined ( -- rules )
    leq-solver-chrat chrat-min append ;
{ LH{ { builtins V{ { = M 1 } } } } }
[ combined { { min 1 1 M } } run-chr-query >old-builtins ] unit-test

{ t }
[ combined { { min 1 2 M } } run-chr-query >old-builtins builtins of { = M 1 } swap in? ] unit-test

{ t }
[ combined { { min 2 1 M } } run-chr-query >old-builtins builtins of { = M 1 } swap in? ] unit-test

{ t }
[ combined { { min A A M } } run-chr-query >old-builtins builtins of { = M A } swap in? ] unit-test

{
    H{
        { builtins V{ { = Z X } } }
        { 1 P{ leq Z Y } }
    }
}
[ combined { { leq X Y } { min X Y Z } } run-chr-query >old-builtins >hashtable ] unit-test

! * Comparison example
! Example: comparisons
! #+begin_example
! export le/2, ge/2, lt/2, gt/2, ne/2.

! ne(X, X) <=> false.
! lt(X, Y) \ ask(ne(X, Y)) <=> entailed(ne(X, Y)).

! le(X, X) <=> true.
! le(X, Y), le(Y, X) <=> X = Y.
! le(X, Y), le(Y, Z) ==> le(X, Z).
! le(X, Y) \ le(X, Y) <=> true.

! le(X, Y) \ ask(le(X, Y)) <=> entailed(le(X, Y)).
! lt(X, Y) \ ask(le(X, Y)) <=> entailed(lt(X, Y)).

! ge(X, Y) <=> le(Y, X).

! le(X, Y) \ ask(ge(Y, X)) <=> entailed(ge(Y, X)).

! le(X, Y), ne(X, Y) <=> lt(X, Y).

! lt(X, X) <=> false.
! lt(X, Y)  ==> le(Y, Z) | lt(X, Z).
! lt(X, Y) \ lt(X, Y) <=> true.

! lt(X, Y) \ ask(lt(X, Y)) <=> entailed(lt(X, Y)).

! gt(X, Y) <=> lt(Y, X).
! #+end_example

TUPLE: le < chr-pred x y ;
TUPLE: ge < chr-pred x y ;
TUPLE: lt < chr-pred x y ;
TUPLE: gt < chr-pred x y ;
TUPLE: ne < chr-pred x y ;
CHRAT: chrat-comp { le ge lt gt ne }
    CHR{ // { ne ?x ?x } -- | false }
    CHR{ { lt ?x ?y } // { ask { ne ?x ?y } } -- | { entailed { ne ?x ?y } } }
    CHR{ // { le ?x ?x } -- | }
    CHR{ { le ?x ?y } // { le ?y ?x } -- | [ ?x ?y ==! ] }
    CHR{ { le ?x ?y } { le ?y ?z } // -- | { le ?x ?z } }
    CHR{ { le ?x ?y } // { ask { le ?x ?y } } -- | { entailed { le ?x ?y } } }
    CHR{ { lt ?x ?y } // { ask { le ?x ?y } } -- | { entailed { lt ?x ?y } } }

    ! Normalize
    CHR{ // { ge ?x ?y } -- | { le ?y ?x } }

    CHR{ { le ?x ?y } // { ask { ge ?y ?x } } -- | { entailed { ge ?y ?x } } }

    CHR{ // { le ?x ?y } { ne ?x ?y } -- | { lt ?x ?y } }

    CHR{ // { lt ?x ?x } -- | false }

    ! Existential guard!
    CHR{ { lt ?x ?y } // -- { le ?y ?z } | { lt ?x ?z } }
    CHR{ { lt ?x ?y } // { lt ?x ?y } -- | }

    ! Normalize
    CHR{ // { gt ?x ?y } -- | { lt ?y ?x } }
;

! * Stack inference

! Intermediate representation language:
TUPLE: Call < state-pred word token ;
TUPLE: CallRet < state-pred word token ;
TUPLE: RecursiveCall < Call back ;

TERM-VARS: ?u ?v ?w ?r ?s ?t ?n ?a ?b ?q ;

! Link helper
TUPLE: Link < chr-pred a b c ;
TUPLE: link-seq < chr-pred pred succ o ;
CHRAT: call-seq { link-seq }
! CHR{ { Word ?s ?t __ } // -- | { Link ?s ?t } }
CHR{ { Link ?s ?t ?u } // { Link ?s ?t ?u } -- | }
! CHR{ { Link ?s ?t ?t } // { Link ?s ?t ?u } -- | { Link ?s ?u ?u } }
! CHR{ { Link ?s ?s ?t } // { Link ?s ?s ?u } -- | { Link ?s ?u ?u } }
! CHR{ // { ask { link-seq ?s ?s ?s } } -- | { entailed { link-seq ?s ?s ?s } } }
CHR{ { Link ?s ?t ?t } // { ask { link-seq ?s ?t ?t } } -- | { entailed { link-seq ?s ?t ?t } } }
CHR{ { Word ?r ?s __ } { Word ?s ?t __ } // { Link ?s ?t ?t } -- | { Link ?r ?s ?s } }
;

! State-specific
TUPLE: Val < state-pred n val ;
TUPLE: Pop < trans-pred val ;
TUPLE: Push < trans-pred val ;
TUPLE: ShiftPush < trans-pred d ;
TUPLE: ShiftPop < trans-pred d ;
TUPLE: Transition < trans-pred ;

! Initial representation
: quot>chr ( callable -- constraints )
    "si" usym 1array over length 1 - [ "s" usym suffix ] times "so" usym suffix
    2 <clumps> [ first2 rot Word boa ] 2map ;

! Minimum-element transition solver.
CHRAT: stack-ops {  }
CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?a } -- | }
CHR{ { Val ?s ?n ?a } // { Val ?s ?n ?b } -- | [ ?b ?a ==! ] }
;

TUPLE: Infer < trans-pred quot ;

CHRAT: infer-stack { Word }
CHR: infer-quot @ { Word ?s ?t ?q } // -- [ ?q callable? ] |  { Infer ?s ?t ?q } ;
CHR: infer-macro @ { Word ?s ?t ?w } // -- [ W{ ?w } macro-quot ] |
    [| | W{ ?w } macro-quot '[ _ call call ] :> body { Word ?s ?t body } ] ;
CHR: infer-recursive @ { Call ?s ?w ?t } // { Word ?u ?v ?w } -- { link-seq ?s ?u ?u } |
    { RecursiveCall ?u ?w ?t ?s } ;
CHR: infer-inline @ // { Word ?s ?t ?w } -- [ W{ ?w } { [ word? ] [ inline? ] } 1&& ] |
    [ W{ ?w } def>> '{ { Word ?s ?u _ } { Call ?s ?w ?x } { CallRet ?s ?w ?x } } ] ;
CHR: infer-literal @ { Word ?s ?t ?w } // -- | { Push ?s ?t ?w } ;
;

! * Type inference, modular
! Context
TUPLE: Disjoint < chr-pred s1 s2 ;
TUPLE: Sub < chr-pred val s ;
TUPLE: Nosub < chr-pred val s ;
CHRAT: solve-sub { Disjoint Sub Nosub }
! CHR{ { Sub ?v ?s } { Nosub ?v ?s } // { Instance ?v ?s } -- | }
CHR{ { Sub ?v ?s } { Nosub ?v ?t } // { Instance ?v ?s } -- | }
CHR{ { = ?v ?x } { Nosub ?x ?y } // -- | { Nosub ?v ?y } }
CHR{ { = ?v ?x } { Sub ?x ?y } // -- | { Sub ?v ?y } }

;

! * Building constraints based on words
! GENERIC: word-constraints ( state-in state-out word -- seq )
! M:: \ if word-constraints ( si so word )
!     gen{ "c" "then" "else" |
!          { Val si 2 "c" }
!          { Val si 1 "then" }
!          { Val si 0 "else" }
!          { Instance "c" boolean }
!          { Instance "then" callable }
!          { Instance "else" callable }
!     } ;
