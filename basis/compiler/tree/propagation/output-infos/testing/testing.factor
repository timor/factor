USING: accessors assocs combinators combinators.short-circuit compiler
compiler.tree compiler.tree.builder compiler.tree.combinators
compiler.tree.normalization compiler.tree.propagation.inlining
compiler.tree.propagation.mutually-recursive.interface compiler.tree.recursive
compiler.units kernel locals namespaces sequences words ;
IN: compiler.tree.propagation.output-infos.testing


: with-opt ( quot -- )
    H{ { propagate-recursive? t }
       { nested-compilation? t } } swap with-variables ; inline

! Uncomment stuff for more details
: with-watched-words ( words quot -- )
    {
        ! [ drop [ reset ] each ]
        ! [ drop [ watch ] each ]
        [ nip call ]
        ! [ drop [ reset ] each ]
    } 2cleave
    ; inline

: test-output-infos ( words -- infos )
    [
        { compile-word maybe-compile-word nested-compile inline-nested-compilation inline-recursive-call }
        [ recompile ] with-watched-words
        drop ]
    [ [ dup "output-infos" word-prop ] map>alist ] bi ;

: normalized-tree ( quot/word -- nodes )
    build-tree analyze-recursive normalize ;


! Return all call nodes to word.
:: calls-to ( nodes word -- seq )
    V{ } clone nodes [ dup { [ #call? ] [ word>> word = ] } 1&&
    [ suffix! ]
    [ drop ] if ] each-node ;

! : prune-branch ( #branch flags -- #branch )
!     '[ _ select-children ] change-children ;

! Expects only one recursive call per branch
! :: inline-call ( nodes rcall -- nodes' )
!     f:> found!
!     nodes
!     [ clone rcall over branch-with-call?
!       [
!           prune-branch t found!
!     ] ]

! :: inline-call ( nodes call-site -- nodes' )
!     nodes [ clone call-site over = [ nodes pruned-recursion-inline-body ] when ]
!     map-nodes ;

! : inline-calls-to ( nodes word -- nodes' )
!     dupd calls-to
!     [ inline-call ] each ;

! Inline all call nodes to word, return the modified tree.  Note that this does
! not produce valid code, and is meant for debugging the structure.
! : inline-calls ( nodes calls -- nodes' )
!     [ swap ensure-reject-call ] each ;

! : inline-calls-to ( nodes word -- nodes )
!     dupd calls-to inline-calls ;
