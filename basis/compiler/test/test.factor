! Copyright (C) 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs classes combinators compiler.cfg
compiler.cfg.debugger compiler.cfg.def-use compiler.cfg.linearization
compiler.cfg.registers compiler.cfg.representations.preferred compiler.cfg.rpo
compiler.cfg.stacks compiler.cfg.stacks.local compiler.cfg.utilities
compiler.tree compiler.tree.builder compiler.tree.checker compiler.tree.cleanup
compiler.tree.combinators compiler.tree.dead-code compiler.tree.debugger
compiler.tree.def-use compiler.tree.escape-analysis compiler.tree.normalization
compiler.tree.optimizer compiler.tree.propagation
compiler.tree.propagation.branches compiler.tree.propagation.copy
compiler.tree.propagation.escaping compiler.tree.propagation.info
compiler.tree.propagation.info.private compiler.tree.propagation.nodes
compiler.tree.propagation.recursive compiler.tree.propagation.slot-refs
compiler.tree.recursive compiler.tree.tuple-unboxing compiler.units
continuations formatting generic hashtables inspector io kernel math mirrors
namespaces prettyprint sequences stack-checker stack-checker.values
tools.annotations tools.test tools.test.private vectors vocabs words ;
IN: compiler.test

: decompile ( word -- )
    dup def>> 2array 1array t t modify-code-heap ;

: recompile-all ( -- )
    all-words compile ;

: compile-call ( quot -- )
    [ dup infer define-temp ] with-compilation-unit execute ;

<< \ compile-call t "no-compile" set-word-prop >>

: init-cfg-test ( -- )
    reset-vreg-counter begin-stack-analysis
    <basic-block> dup basic-block set begin-local-analysis
    H{ } clone representations set
    H{ } clone replaces set ;

: cfg-unit-test ( result quot -- )
    '[ init-cfg-test @ ] unit-test ; inline

: edge ( from to -- )
    [ get ] bi@ 1vector >>successors drop ;

: edges ( from tos -- )
    [ get ] [ [ get ] V{ } map-as ] bi* >>successors drop ;

: test-diamond ( -- )
    0 1 edge
    1 { 2 3 } edges
    2 4 edge
    3 4 edge ;

: resolve-phis ( bb -- )
    [
        [ [ [ get ] dip ] assoc-map ] change-inputs drop
    ] each-phi ;

: test-bb ( insns n -- )
    [ insns>block dup ] keep set resolve-phis ;

: fake-representations ( cfg -- )
    post-order [
        instructions>> [
            [ [ temp-vregs ] [ temp-vreg-reps ] bi zip ]
            [ [ defs-vregs ] [ defs-vreg-reps ] bi zip ]
            bi append
        ] map concat
    ] map concat >hashtable representations set ;

: count-insns ( quot insn-check -- ? )
    [ test-regs [ cfg>insns ] map concat ] dip count ; inline

: contains-insn? ( quot insn-check -- ? )
    count-insns 0 > ; inline

: make-edges ( block-map edgelist -- )
    [ [ of ] with map first2 connect-bbs ] with each ;

: propagated-tree ( quot -- nodes )
    build-tree analyze-recursive normalize propagate compute-def-use dup check-nodes ;

: optimize-quot ( quot -- quot' )
    build-tree
    analyze-recursive
    normalize
    propagate
    cleanup-tree
    escape-analysis
    unbox-tuples
    compute-def-use
    remove-dead-code
    "no-check" get [ dup check-nodes ] unless nodes>quot ;

: final-info ( quot -- seq )
    build-tree
    analyze-recursive
    normalize
    propagate
    compute-def-use
    dup check-nodes
    last node-input-infos ;

! Don't clean up, also retrieve the value info from the state, not the annotation
: final-value-info ( quot -- seq )
    propagated-tree
    last in-d>> [ value-info ] map ;

: final-classes ( quot -- seq )
    final-info [ class>> ] map ;

: final-literals ( quot -- seq )
    final-info [ literal>> ] map ;

: init-values ( -- )
    H{ } clone copies set
    H{ } clone 1vector value-infos set
    init-escaping-values
    HS{ } clone virtual-values set
    IH{ } clone literal-values set
    ;

: with-values ( quot -- )
    [
      10000 debug-value-counter set-global
      debug-counter on
      init-values
    ] prepose with-scope ; inline

: with-rw ( quot -- )
    propagate-rw-slots [
        120 recursion-limit set
        with-values
    ] with-variable-on ; inline

: with-rw-prop ( quot -- )
    [ propagate-rw-slots on check-optimizer? on ] prepose
    [ propagate-rw-slots off check-optimizer? off ] [ ] cleanup ; inline
    ! [ init-values ] prepose propagate-rw-slots swap with-variable-on ; inline

: hack-unit-tests ( -- )
    \ (unit-test) [ [ [ with-rw-prop ] curry ] prepose ] annotate ;

: annotate-generalize-counter ( -- )
    \ generalize-counter dup reset
    [ [ "--- Entering generalize-counter" print 2dup [ "info': " write ! bake-info
                                                       ... ] [ "initial: " write ! bake-info
                                                               ... ] bi* ] prepose
      [ "--- Leaving generalized-counter: " print dup ! bake-info
        ... ] compose
    ] annotate ;

: watch-value-infos ( seq -- )
    [ dup [ resolve-copy "%d -> %d : " printf ] [ value-info ... ] bi ] each ;

: watch-in-d ( node -- )
    "-- in-d-value-info:" print
    in-d>> watch-value-infos ;

: watch-out-d ( node -- )
    "-- Return: " write dup word>> name>> print
    "-- out-d-value-info:" print
    out-d>> watch-value-infos ;

: annotate-value-info<= ( -- )
    \ value-info<= dup reset [ [ "--- Entering value-info<=" print 2dup [ ... ] bi@ ] prepose
                               [ "--- Leaving value-info<=: " write dup . ] compose ] annotate ;


:: annotate-#call ( node-selector: ( #call -- ? ) -- )
    [ dup #call? node-selector [ drop f ] if ] :> sel
    M\ #call propagate-before dup reset
    [ [ dup describe ] prepose ] annotate ;


: watch-virtuals ( -- )
    inner-values get
    [ [ "virtual %d: " printf ] [ value-info ... ] bi ] [ each ] curry each ;

: annotate-call-recursive ( -- )
    M\ #call-recursive propagate-before dup reset
    [ [ "--- #call-recursive" print watch-virtuals ]
      prepose
     ] annotate ;

: annotate-return-recursive ( -- )
    M\ #return-recursive propagate-before dup reset
    [ [ "--- #return-recursive" print watch-virtuals ]
      prepose
    ] annotate ;

: annotate-virtual-creation ( -- )
    \ slot-info>lazy-info dup reset [
        [ "--- Entering slot-info>lazy-info: " write
          "info: " write pick ... ] prepose
        [ "--- Leaving slot-info>lazy-info:" print " " write
          dup ... ] compose
    ] annotate ;

: watch-node ( node -- )
    dup class-of "Node: %s" printf nl
    <mirror>
    [ "in-d" of [ " in-d:" print watch-value-infos ] when* ]
    [ "out-d" of [ unparse-short " out-d: %s\n" printf ] when* ]
    [ "declaration" of [ unparse "declaration: %s\n" printf ] when* ]
    tri
    ;

: annotate-propagate-around ( -- )
    \ propagate-around dup reset [ [ dup #shuffle?
                                     [ dup watch-node ] unless
                                   ] prepose
    ] annotate ;

: annotate-slot-calls ( -- )
    \ propagate-slot-call* subwords
    [ dup reset watch ] each ;

: watch-copies ( node -- )
    <mirror>
    [
        "in-d" of [
            "in-d:" print
            [ dup resolve-copy " %d <- %d\n" printf ] each
        ] when*
    ]
    [
        "out-d" of [
            [ "out-d: " print . ] unless-empty
        ] when*
    ] bi
    ;

: annotate-copies ( -- )
    \ propagate-around dup reset [
        [ dup
          {
              [ class-of "Propagate: %s " printf ]
              [ dup #call? [ word>> . ] [ drop ] if ]
              [ dup #push? [ literal>> . ] [ drop nl ] if ]
              [ watch-copies ]
          } cleave
        ] prepose
    ] annotate ;

: propagation-trace ( quot/word -- nodes vars )
    \ (lift-inner-values) dup reset watch
    ! \ propagate-after dup reset [ [ "Inner values: " write inner-values get ... ] prepose ] annotate
    \ strong-update dup reset watch
    \ weak-update dup reset watch
    annotate-virtual-creation
    annotate-return-recursive
    annotate-call-recursive
    annotate-slot-calls
    annotate-propagate-around
    ! annotate-copies
    [
        ! [ drop t ] annotate-#call
        [ propagated-tree { copies value-infos } [ dup get ] H{ } map>assoc ] with-values
    ]
    [
        \ (lift-inner-values) reset
        \ propagate-before reset
        \ propagate-around reset
        \ strong-update reset
        \ weak-update reset
        ! \ propagate-after reset
        \ record-inner-value reset
        \ slot-info>lazy-info reset
        \ propagate-slot-call* reset
    ] [ ] cleanup
    ;


: annotate-recursive-stacks ( -- )
    \ recursive-stacks dup reset [
        [ dup class-of "--- recursive stacks for %s:\n" printf ] prepose
        [ 2dup [ "stacks: " write ... ] [ "initial: " write ... ] bi* ] compose
    ] annotate
    \ unify-recursive-stacks dup reset [
        [ "--- unified stacks: " write dup ... ] compose
    ] annotate
    ;

: recursion-trace ( quot/word -- nodes )
    annotate-virtual-creation
    \ propagate-recursive-phi-virtuals dup reset watch
    annotate-recursive-stacks
    annotate-propagate-around
    \ (lift-inner-values) dup reset watch
    M\ #recursive propagate-around dup reset watch
    annotate-value-info<=
    annotate-generalize-counter
    annotate-call-recursive
    \ strong-update dup reset watch
    \ weak-update dup reset watch
    [ drop t ] annotate-#call
    [ [ propagated-tree ] with-values ]
    [
        \ value-info<= reset
        \ generalize-counter reset
        \ propagate-before reset
        \ (lift-inner-values) reset
        \ weak-update reset
        \ strong-update reset
        \ propagate-after reset
        \ propagate-around reset
        \ recursive-stacks reset
        \ unify-recursive-stacks reset
        \ propagate-recursive-phi-virtuals reset
        \ slot-info>lazy-info reset
    ] [  ] cleanup
    ;

: annotate-check-fixed-point ( -- )
    \ check-fixed-point dup reset [
        [ pick class-of "--- Entering check-fixed-point : %s\n" printf
2dup [ "current iteration: " write ... ] [ "last iteration: " write ... ] bi*
] prepose
    ] annotate ;

: annotate-union-lazy-slot ( -- )
    \ union-lazy-slot dup reset [
        [ "--- Union-lazy-slot: " write 2dup [ ... ] bi@ ] prepose
        [ "--- Union-lazy-slot result: " write dup ... ] compose
    ] annotate ;

: fixed-point-trace ( quot/word -- nodes )
    annotate-copies
    annotate-virtual-creation
    annotate-generalize-counter
    ! annotate-value-info<=
    \ value-info<= dup reset watch
    annotate-check-fixed-point
    ! annotate-propagate-around
    annotate-union-lazy-slot
    annotate-recursive-stacks
    \ weak-update dup reset watch
    \ strong-update dup reset watch
    \ propagate-recursive-phi-virtuals dup reset watch
    \ propagate-recursive-phi dup reset watch
    \ generalize-counter-slot dup reset watch
    \ generalize-lazy-counter-slot dup reset watch
    [ [ propagated-tree ] with-values ]
    [
        \ generalize-counter reset
        \ propagate-around reset
        \ value-info<= reset
        \ slot-info>lazy-info reset
        \ weak-update reset
        \ strong-update reset
        \ check-fixed-point reset
        \ propagate-recursive-phi-virtuals reset
        \ propagate-recursive-phi reset
        \ union-lazy-slot reset
        \ recursive-stacks reset
        \ unify-recursive-stacks reset
        \ generalize-counter-slot reset
        \ generalize-lazy-counter-slot reset
    ] [  ] cleanup ;


! Converting lazy info stuff back into regular info for comparisons
! Must be baked!
GENERIC: >regular-info ( value-info -- valu-info )
M: f >regular-info ;
M: value-info-state >regular-info
    clone f >>origin
    [ [ >regular-info dup object-info = [ drop f ] when ] map >vector dup [ ] any? [ drop f ] unless ] change-slots
    [ >regular-info dup object-info = [ drop f ] when ] change-summary-slot ;
M: lazy-info >regular-info
    cached>> >regular-info ;


: tree-size ( nodes -- n )
    0 swap [ drop 1 + ] each-node ;

: report-difference ( tree1 tree2 -- tree2 )
    [ [ tree-size ] bi@ 2dup =
      [ 2drop ]
      [ "-- Nodes differ! :%d %d" printf flush ] if
    ] keep ;

: report-info-difference ( word tree1 tree2 -- )
    [ last node-input-infos [ >regular-info ] map ] bi@ 2dup = [ 3drop ]
    [ "Infos differ: " print rot . [ ... ] bi@ ] if ;

: compare-rw-nodes ( quot/word -- )
    dup [ build-tree optimize-tree ]
    [ [ build-tree optimize-tree ] with-rw-prop ] bi
    2dup [ tree-size ] bi@ = [ "Tree size differ:" print pick . ] unless
    report-info-difference ;

: compare-rw-opt. ( quot/word -- )
    [ optimized. ]
    [ [ optimized. ] with-rw-prop ] bi ;

: compare-rw-word ( quot/word -- )
    dup generic? [ subwords [ compare-rw-nodes ] each ] [ compare-rw-nodes ] if ;
