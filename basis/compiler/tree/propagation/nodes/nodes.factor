! Copyright (C) 2004, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors assocs compiler.tree
compiler.tree.propagation.copy compiler.tree.propagation.info
namespaces
combinators
kernel sequences ;
IN: compiler.tree.propagation.nodes

GENERIC: propagate-before ( node -- )

GENERIC: propagate-after ( node -- )

GENERIC: annotate-node ( node -- )

GENERIC: propagate-around ( node -- )

! TODO For tracking input escaping
GENERIC: propagate-escape ( node -- )

GENERIC: propagate-origin ( node -- )

: (propagate) ( nodes -- )
    [ [ compute-copy-equiv ] [ propagate-around ] bi ] each ;

: extract-value-info ( values -- assoc )
    [ dup value-info ] H{ } map>assoc ;

! TODO: remove this after debugging
SYMBOL: bake-lazy-infos
! bake-lazy-infos [ t ] initialize

: (annotate-node) ( node values -- )
    extract-value-info [
        propagate-rw-slots?
        bake-lazy-infos get and
        [ bake-info ] when
    ] assoc-map
    >>info drop ; inline

: (annotate-node-baked) ( node values -- )
    bake-lazy-infos
    [ (annotate-node) ] with-variable-on ; inline

M: node propagate-before drop ;

M: node propagate-after drop ;

M: node annotate-node drop ;

M: node propagate-origin drop ;

M: node propagate-around
    {
        ! Calculate output value information based on input information
        [ propagate-before ]
        [ propagate-rw-slots? [ propagate-origin ] [ drop ] if ]
        ! Update the set of escaping values, modify values if they escape ( TODO: probably needs to go after annotation... )
        ! Store calculated info at nodes
        [ annotate-node ]
        ! Update subsequent propagation calls with known additional infos
        [ propagate-after ]
    } cleave ;
