USING: accessors assocs chr chr.factor chr.factor.conditions chr.factor.control
chr.factor.words chr.parser chr.state kernel match namespaces sequences sets
terms words ;

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

! Insert at least one dummy state to prevent hooking into the top node with Entry specs
CHR: instantiate-rules @ // { ApplyWordRules ?s ?t ?w } -- |
! { Stack ?s ?rho }
! { Stack ?s0 ?rho } { AddLink ?s ?s0 }
! [ ?s0 ?t ?w instantiate-word-rules ]
[ ?s ?t ?w instantiate-word-rules ]
    ;



! Erase inner state-specific info, so we can treat stacks as conditions
! CHR{ { CompileRule } // { Entry ?s ?w } -- [ ?s ?ground-value +top+ = ] | { TopEntry +top+ ?w } }
! CHR{ { CompileRule } // { Entry ?s ?w } -- [ ?s +top+? not ] | { Cond ?s P{ Inlined ?w } } }
! CHR{ { CompileRule } // { Stack ?s __ } -- [ ?s { +top+ +end+ } in? not ] | }
! CHR{ { CompileRule } // { Val __ __ __ } -- | }
! CHR{ { CompileRule } // { FoldQuot __ __ __ __ } -- | }
! CHR{ { CompileRule } // { LitStack __ __ __  } -- | }
CHR{ { CompileRule } // { AskLit __ __  } -- | }
! CHR{ { CompileRule } // { CondRet __ __ __  } -- | }
! CHR{ { CompileRule } // { Dead __ } -- | }
! CHR{ { CompileRule } // { Lit ?x __ } { Instance ?x __ } -- | }
! CHR{ { CompileRule } // { InlineUnknown ?s ?t ?x } -- | { Cond ?s { InlinesUnknown ?x } } }
! CHR: remove-words-1 @ { CompileRule } // { Generic __ __ __ } -- | ;
CHR: remove-words-2 @ { CompileRule } // { Word __ __ __ } -- | ;

! Erase Simplification artefacts

CHR{ // { CompileRule } -- | { CompileDone } }

CHR{ { CompileDone } // { Absurd __ } -- | }

CHR{ // { CompileDone } -- | }
;
