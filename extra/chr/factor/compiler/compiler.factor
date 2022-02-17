USING: accessors assocs chr chr.factor chr.factor.words chr.state kernel match
namespaces sequences sets terms words ;

IN: chr.factor.compiler

FROM: syntax => _ ;
FROM: namespaces => set ;

! * Compiler interface for chrat-based Interference of Factor code

: constraints>body ( store -- constraint )
    ! Make sure we convert the body vars in a fresh scope
    defined-equalities-ds [ values rest fresh [ term-vars ] keep <generator> ] with-variable-off ;

SYMBOL: rules-cache
SYMBOL: inline-history
: with-jit-compile ( quot -- )
    [ H{ } clone rules-cache set
      V{ } clone inline-history set ] prepose with-scope ; inline

ERROR: recursive-chrat-compile word ;
: (chrat-compile) ( quot/word -- constraints )
    dup inline-history get in? [ recursive-chrat-compile ] when
    inline-history [ over suffix ] change
    '{ { ChratInfer _ } { CompileRule } } run-chrat-query
    constraints>body ;

: chrat-compile-def ( word -- )
    dup "chrat-rules" remove-word-prop
    dup (chrat-compile) "chrat-rules" set-word-prop ;

: chrat-word-rules ( word -- constraint )
    ! "chrat-rules" word-prop ;
    rules-cache get [ (chrat-compile) ] cache ;
    ! dup "chrat-rules" word-prop [ nip ]
    ! [ dup (chrat-compile) [ "chrat-rules" set-word-prop ] ]

:: instantiate-word-rules ( r s w -- new )
    w chrat-word-rules
    ! w "chrat-rules" word-prop
    [ dup vars>>
      import-vars
      ! drop
      H{ { +top+ r } { +end+ s } } [ replace-partial? on replace-patterns ] with-variables ] [ f ] if* ;
    ! valid-match-vars [ lift ] with-variable-off ;

: chrat-compile ( quot/word -- constraints )
    [ (chrat-compile) ] with-jit-compile ;

: chrat-infer ( quot/word -- constraints )
    [ '{ { ChratInfer _ } } run-chrat-query ] with-jit-compile ;
