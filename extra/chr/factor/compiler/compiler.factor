USING: accessors assocs chr chr.factor chr.factor.dead-code chr.factor.types
chr.parser chr.state kernel match namespaces sequences sets sets.extras terms
types.util words ;

IN: chr.factor.compiler

FROM: syntax => _ ;
FROM: namespaces => set ;

! * Compiler interface for chrat-based Interference of Factor code

! ** Create Rules for instantiation
TUPLE: CompileRule < chr-pred ;
TUPLE: CompileDone < chr-pred ;
TUPLE: InferMode < chr-pred ;

! * Factor Side and Interface
: constraints>body ( store -- constraint )
    ! Make sure we convert the body vars in a fresh scope
    f defined-equalities-ds [ fresh [ term-vars ] keep <generator> ] with-global-variable ;

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
    values rest { StartGC } suffix \ dead-code swap query-with
    values rest constraints>body ;

! : chrat-compile-def ( word -- )
!     dup "chrat-rules" remove-word-prop
!     dup (chrat-compile) "chrat-rules" set-word-prop ;

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
    ! defined-equalities .
    w chrat-word-rules
    ! w "chrat-rules" word-prop
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


CHRAT: compile-rules { }

CHR: infer-done @ { CompileRule } // { InferMode } -- | ;

! CHR: query-types @ { CompileRule } { Scope +top+ +end+ ?rho ?sig __ } // -- |
! [ ?rho list>array* ?sig list>array* symmetric-diff
!  [ "tau" uvar <term-var> Type boa ] map ] ;

CHR: define-top-stacks @ { CompileRule } // { Scope +top+ +end+ ?rho ?sig __ } -- | { Stack +top+ ?rho } { Stack +end+ ?sig } ;

! CHR: assign-atomic-container-types @ { CompileRule } // { Type ?x ?tau } { Subtype ?tau A{ ?sig } } -- | { Type ?x ?sig } ;

! NOTE: We can treat these literals as dead if we don't care about the call.
! CHR: partial-fold-lits-are-dead @ { CompileRule } { FoldCall __ __ ?i __ } // { --> __ P{ is ?x A{ ?v } } } -- [ ?x ?i known in? ] | ;
! CHR: partial-fold-lits-are-dead @ { CompileRule } <={ Call __ __ ?i . __ } { is ?x A{ ?v } } // -- [ ?x ?i known in? ] | { Dead ?x } ;

! CHR: assume-top-again @ { CompileRule } // AS: ?p <={ val-pred __ . __ } -- [ ?p Dead? not ] | { --> +top+ ?p } ;

CHR: rm-stacks @ { CompileRule } // { Stack ?s __ } -- [ ?s +top+ = not ] [ ?s +end+ = not ] | ;

! *** Erase Simplification artifacts

! CHR{ { CompileRule } // { Dead __ } -- | }
! CHR{ { CompileRule } // { AskLit __ __ } -- | }

CHR{ // { CompileRule } -- | { CompileDone } }

CHR{ { CompileDone } // { Dead __ } -- | }

CHR{ // { CompileDone } -- | }
;
