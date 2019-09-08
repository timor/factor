USING: classes classes.algebra classes.algebra.private classes.parser
classes.predicate combinators.short-circuit compiler.tree.propagation.info
sets
continuations kernel lexer locals math.intervals parser sequences words ;
IN: math.intervals.predicates

ERROR: invalid-interval-definition stack ;

PREDICATE: empty-interval-class < word empty-interval eq? ;
UNION: valid-interval interval full-interval empty-interval-class ;
PREDICATE: interval-predicate-class < predicate-class "declared-interval" word-prop ;

! Class Algebra Considerations

! If two or mode interval predicate classes are defined on the same parent
! class, it is possible to specify an order on this set of classes.  However, if
! this is done globally, this would interact in uncontrollable ways.  Predicates
! don't define an order at all per default, so per default, no dispatch inlining
! is performed at all.
! To get around that, there could be several approaches:
! 1: Assign predicate classes to contexts.  In these contexts, total order of
! all defined classes would be enforced, so that dispatch can be optimized.
! If two classes are assigned to the same context, they are considered
! comparable.  However, this is not straightforward to implement if a static
! dispatch is supposed to be maintained.
! 2: Expect the user to define interval-classes explicitly as subclasses of
! other interval classes.  This is the easiest way, because nothing would have
! to be changed, maybe a sanity check inserted that no empty intervals would be
! created.  This would mean that existing definitions can not be used easily, as
! they would have to be re-defined on a different superclass if they are to be
! used alongside a larger interval-predicate class.


<PRIVATE
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
