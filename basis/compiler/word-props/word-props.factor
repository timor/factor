USING: combinators.short-circuit generic generic.single kernel macros
stack-checker.errors stack-checker.inlining words ;
IN: compiler.word-props



: compile? ( word -- ? )
    ! Don't attempt to compile certain words.
    {
        [ "forgotten" word-prop ]
        [ inlined-block? ]
    } 1|| not ;

GENERIC: no-compile? ( word -- ? )

M: method no-compile? "method-generic" word-prop no-compile? ;

M: predicate-engine-word no-compile? "owner-generic" word-prop no-compile? ;

M: word no-compile?
    { [ macro? ] [ "special" word-prop ] [ "no-compile" word-prop ] } 1|| ;

GENERIC: combinator? ( word -- ? )

M: method combinator? "method-generic" word-prop combinator? ;

M: predicate-engine-word combinator? "owner-generic" word-prop combinator? ;

M: word combinator? inline? ;

: ignore-error? ( word error -- ? )
    ! Ignore some errors on inline combinators, macros, and special
    ! words such as 'call'.
    {
        [ drop no-compile? ]
        [ [ combinator? ] [ unknown-macro-input? ] bi* and ]
    } 2|| ;

: optimize? ( word -- ? )
    {
        [ single-generic? ]
        [ primitive? ]
    } 1|| not ;
