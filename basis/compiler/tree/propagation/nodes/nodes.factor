! Copyright (C) 2004, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors assocs combinators compiler.tree
compiler.tree.propagation.copy compiler.tree.propagation.info
kernel sequences ;
IN: compiler.tree.propagation.nodes

GENERIC: propagate-before ( node -- )

GENERIC: propagate-after ( node -- )

GENERIC: annotate-node ( node -- )

GENERIC: propagate-around ( node -- )

GENERIC: annotate-inputs ( node -- )

: (propagate) ( nodes -- )
    [ [ compute-copy-equiv ] [ propagate-around ] bi ] each ;

: extract-value-info ( values -- assoc )
    [ dup value-info ] H{ } map>assoc ;

: (annotate-node) ( node values -- )
    extract-value-info >>info drop ; inline

: (annotate-node-also) ( node values -- )
    extract-value-info swap [ swap assoc-union ] change-info drop ;

: (annotate-in-d) ( node -- )
    dup in-d>> (annotate-node-also) ;

M: node annotate-inputs drop ;

M: #call annotate-inputs
    (annotate-in-d) ;

M: node propagate-before drop ;

M: node propagate-after drop ;

M: node annotate-node drop ;

M: node propagate-around
    {
        [ annotate-inputs ]
        [ propagate-before ]
        [ annotate-node ]
        [ propagate-after ]
    } cleave ;
