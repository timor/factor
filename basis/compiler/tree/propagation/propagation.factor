! Copyright (C) 2004, 2008 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: arrays
compiler.tree
compiler.tree.propagation.branches
compiler.tree.propagation.call-effect
compiler.tree.propagation.constraints
compiler.tree.propagation.copy
compiler.tree.propagation.escaping
compiler.tree.propagation.info
compiler.tree.propagation.inlining
compiler.tree.propagation.known-words
compiler.tree.propagation.nodes
compiler.tree.propagation.recursive
compiler.tree.propagation.reflinks
compiler.tree.propagation.simple
compiler.tree.propagation.set-slots
compiler.tree.propagation.slot-refs
compiler.tree.propagation.transforms
kernel namespaces ;
IN: compiler.tree.propagation

: propagate ( nodes -- nodes )
    H{ } clone copies set
    H{ } clone 1array value-infos set
    H{ } clone 1array constraints set
    ! orphan get
    ! [ introduce-value ]
    ! [ object-info swap set-value-info ] bi
    init-escaping-values
    unknown-ref introduce-escaping-value
    IH{ } clone literal-values set
    dup (propagate) ;
