! Copyright (C) 2008 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel namespaces
accessors
combinators.short-circuit
compiler.tree
compiler.tree.recursive
compiler.tree.normalization
compiler.tree.propagation
compiler.tree.propagation.info
compiler.tree.cleanup
compiler.tree.escape-analysis
compiler.tree.escape-analysis.check
compiler.tree.tuple-unboxing
compiler.tree.identities
compiler.tree.def-use
compiler.tree.dead-code
compiler.tree.modular-arithmetic
compiler.tree.finalization
compiler.tree.checker
io math sequences words ;
IN: compiler.tree.optimizer

SYMBOL: word-being-compiled

SYMBOL: check-optimizer?

: ?check ( nodes -- nodes' )
    check-optimizer? get [
        dup check-nodes
    ] when ;

! TODO: find better place for stuff below
ERROR: duplicate-output-infos word infos ;

: should-store-output-infos? ( nodes -- infos/f )
    ! 2 tail* first2              ! last2
    [
      { [ length 2 > ] [ but-last last ] } 1&&
      #terminate? not
    ]
    [ last dup #return?
      [ "STRANGE: last node not return, not storing outputs" print ] unless
      node-input-infos
    ]
    bi and ;

: replace-literal-infos ( infos -- infos )
    [ dup literal?>> [ drop object-info ] when ] map ;

: update-output-infos ( nodes -- nodes )
    word-being-compiled get [
        dup "output-infos" word-prop [ duplicate-output-infos ] when*
        over should-store-output-infos?
        [
            [ drop ] [
                [ clone f >>literal? ] map ! This line prevents only literal value propagation
                ! replace-literal-infos      ! This line prevents literal value info propagation completely
                "output-infos" set-word-prop
            ] if-empty
        ] [
            drop
        ] if*
    ] when* ;

: optimize-tree ( nodes -- nodes' )
    [
        analyze-recursive
        normalize
        propagate
        cleanup-tree
        dup run-escape-analysis? [
            escape-analysis
            unbox-tuples
        ] when
        apply-identities
        compute-def-use
        remove-dead-code
        ?check
        compute-def-use
        optimize-modular-arithmetic
        finalize
        update-output-infos
    ] with-scope ;
