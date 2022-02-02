USING: chr chr.parser chr.state kernel linked-assocs match tools.test ;
IN: chr.modular.tests

TUPLE: leq < chr-pred v1 v2 ;

SYMBOLS: A B C ;

MATCH-VARS: ?x ?y ?z ;

TUPLE: eq < chr-pred v1 v2 ;
! Equality solver from schrijvers paper
MATCH-VARS: ?x1 ?y1 ?x2 ?y2 ;
CONSTANT: eq-solver {
    CHR: reflexive @ // { eq ?x ?y } -- { = ?x ?y } | ;
CHR: redundant @ { eq ?x1 ?y1 } // { eq ?x2 ?y2 } -- { = ?x1 ?x2 } { = ?y1 ?y2 } | ;
CHR: symmetric @ { eq ?x ?y } // -- | { eq ?y ?x } ;
CHR: transitive @ { eq ?x1 ?y1 } { eq ?x2 ?y2 } // -- { = ?y1 ?x2 } | { eq ?x1 ?y2 } ;
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
    CHR: reflexivity @ // { leq ?x ?y } -- { = ?x ?y } | ;
CHR: antisymmetry @ // { leq ?x ?y } { leq ?y ?x } -- | { = ?x ?y } ;
CHR: transitivity @ { leq ?x ?y } { leq ?y ?z } // -- | { leq ?x ?z } ;
}

{
    LH{ { 1 P{ leq A B } }
        { 2 P{ leq C A } }
        { 5 P{ leq C B } }
        { 6 { = C B } } }
}
[ leq-solver-orig { { leq A B } { leq C A } { leq B C } } run-chr-query ] unit-test

! This is the example from the CHRat paper
! rule-name @ Hk... \ Hr... <=> G.. | B ;
! CHR{ Hk.. // Hr.. -- G.. | B }
CONSTANT: leq-solver-chrat {
    CHR{ // { leq ?x ?x } -- | }
    CHR{ // { leq ?x ?y } { leq ?y ?x } -- | { = ?x ?y } }
    CHR{ { leq ?x ?y } { leq ?y ?z } // -- | { leq ?x ?z } }
    CHR{ { leq ?x ?y } // { leq ?x ?y } -- | }
}

{
    LH{ { 1 P{ leq A B } }
        { 2 P{ leq C A } }
        { 5 P{ leq C B } }
        { 6 { = C B } } }
}
[ leq-solver-chrat { { leq A B } { leq C A } { leq B C } } run-chr-query ] unit-test
