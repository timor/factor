USING: accessors assocs chr chr.factor chr.factor.conditions chr.factor.types
chr.parser chr.state kernel match namespaces sequences sets sets.extras terms
types.util words ;

IN: chr.factor.compiler

FROM: syntax => _ ;
FROM: namespaces => set ;

! * Compiler interface for chrat-based Interference of Factor code

! ** Create Rules for instantiation
TUPLE: CompileRule < chr-pred ;
TUPLE: CompileDone < chr-pred ;

! * Factor Side and Interface
: constraints>body ( store -- constraint )
    ! Make sure we convert the body vars in a fresh scope
    f defined-equalities-ds [ values rest fresh [ term-vars ] keep <generator> ] with-global-variable ;

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
    rules-cache get [
        f defined-equalities-ds [ (chrat-compile) ] with-global-variable
    ] cache ;
    ! dup "chrat-rules" word-prop [ nip ]
    ! [ dup (chrat-compile) [ "chrat-rules" set-word-prop ] ]

: instantiate-scope ( generator assoc -- generator )
    [ replace-partial? on replace-patterns ] with-variables ;

:: instantiate-word-rules ( r s w -- new )
    ! "haha" .
    ! defined-equalities .
    w chrat-word-rules
    ! w "chrat-rules" word-prop
    ! "foo" .
    ! defined-equalities .
    [ dup vars>>
      import-vars
      ! drop
      H{ { +top+ r } { +end+ s } } instantiate-scope ] [ f ] if* ;
    ! valid-match-vars [ lift ] with-variable-off ;

: chrat-compile ( quot/word -- constraints )
    [ (chrat-compile) ] with-jit-compile ;

: chrat-infer ( quot/word -- constraints )
    [ '{ { ChratInfer _ } } run-chrat-query ] with-jit-compile ;

! * Chrat side


CHRAT: compile-rules { CompileRule }

CHR: query-types @ { CompileRule } { Scope +top+ +end+ ?rho ?sig __ } // -- |
[ ?rho list>array* ?sig list>array* symmetric-diff
 [ "tau" uvar <term-var> Type boa ] map ] ;

CHR: rm-states @ { CompileRule } // <={ state-pred ?s . __ } -- [ ?s +top+ = not ] [ ?s +end+ = not ] | ;

CHR: define-top-stacks @ { CompileRule } // { Scope +top+ +end+ ?rho ?sig __ } -- | { Stack +top+ ?rho } { Stack +end+ ?sig } ;

! Erase Simplification artifacts

CHR{ { CompileRule } // { Dead __ } -- | }

CHR{ // { CompileRule } -- | { CompileDone } }

CHR{ { CompileDone } // { Absurd __ } -- | }
! Relies on all conditions having propagated to their leaders!
! CHR{ { CompileDone } { Trivial ?s } // { CondJump __ ?s } -- | }
CHR{ { CompileDone } // { Trivial __ } -- | }
! CHR{ { CompileDone } // { CondRet __ __ } -- | }

! Only keep top conditions!
! CHR: only-top-conds @ { CompileDone } // SUB: ?x cond-pred L{ ?c . __ } -- [ ?c known +top+? not ] | ;

CHR{ // { CompileDone } -- | }
;
