USING: classes classes.parser classes.predicate combinators.short-circuit
continuations kernel lexer locals math.intervals parser sequences words ;
IN: math.intervals.predicates

ERROR: invalid-interval-definition stack ;

<PRIVATE
PREDICATE: empty-interval-class < word empty-interval eq? ;
UNION: valid-interval interval full-interval empty-interval-class ;

: evaluate-interval ( quot -- interval )
    { } swap with-datastack
    dup { [ length 1 = ] [ first valid-interval? ] } 1&&
    [ first ]
    [ invalid-interval-definition ] if ;

:: interval>predicate ( superclass interval -- quot: ( obj -- ? ) )
    [ { [ superclass instance? ] [ interval interval-contains? ] } 1&& ] ;
PRIVATE>

: define-interval-predicate-class ( class superclass interval -- )
    [ dupd interval>predicate define-predicate-class ]
    [ nip "declared-interval" set-word-prop ]
    [ 2drop predicate-word t "inline" set-word-prop ]
    3tri ;

SYNTAX: INTERVAL-PREDICATE:
    scan-new-class "<" expect scan-class parse-definition
    evaluate-interval define-interval-predicate-class ;

PREDICATE: interval-predicate-class < predicate-class "declared-interval" word-prop ;
