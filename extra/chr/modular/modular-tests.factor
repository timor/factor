USING: tools.test chr.modular chr.parser ;
IN: chr.modular.tests

TUPLE: leq < chr-pred v1 v2 ;

SYMBOLS: A B C ;

MATCH-VARS: ?x ?y ?z ;
CONSTANT: leq-solver {
    CHR{ // { leq ?x ?x } -- | }
    CHR{ // { leq ?x ?y } { leq ?y ?x } -- | { = ?x ?y } }
    CHR{ { leq ?x ?y } { leq ?y ?z } // -- | { leq ?x ?z } }
    CHR{ { leq ?x ?y } // { leq ?x ?y } -- | }
}
