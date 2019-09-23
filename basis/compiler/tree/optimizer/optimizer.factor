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
compiler.tree.propagation.simple
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
compiler.tree.propagation.info.present
io math sequences words ;
IN: compiler.tree.optimizer

SYMBOL: word-being-compiled
SYMBOL: post-propagate

SYMBOL: check-optimizer?

: ?check ( nodes -- nodes' )
    check-optimizer? get [
        dup check-nodes
    ] when ;

! TODO: find better place for stuff below
ERROR: duplicate-output-infos word infos ;

: replace-literal-infos ( infos -- infos )
    [ dup literal?>> [ drop object-info ] when ] map ;

: optimize-tree ( nodes -- nodes' )
    [
        analyze-recursive
        normalize
        propagate
        post-propagate get [ call( nodes -- nodes ) ] when*
        cleanup-tree
        ! Stop, recalculate where output info is missing!
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
    ] with-scope ;
