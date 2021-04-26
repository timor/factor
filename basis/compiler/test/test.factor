! Copyright (C) 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs compiler.cfg compiler.cfg.debugger
compiler.cfg.def-use compiler.cfg.linearization compiler.cfg.registers
compiler.cfg.representations.preferred compiler.cfg.rpo compiler.cfg.stacks
compiler.cfg.stacks.local compiler.cfg.utilities compiler.tree.builder
compiler.tree.checker compiler.tree.def-use compiler.tree.normalization
compiler.tree.propagation compiler.tree.propagation.copy
compiler.tree.propagation.escaping compiler.tree.propagation.info
compiler.tree.recursive compiler.units hashtables kernel math namespaces
sequences stack-checker stack-checker.values tools.annotations tools.test
tools.test.private vectors vocabs words ;
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
    build-tree analyze-recursive normalize propagate ;

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
        with-values
    ] with-variable-on ; inline
