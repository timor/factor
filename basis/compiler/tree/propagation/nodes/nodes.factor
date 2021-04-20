! Copyright (C) 2004, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors assocs compiler.tree
compiler.tree.propagation.copy compiler.tree.propagation.info
combinators
kernel sequences ;
IN: compiler.tree.propagation.nodes

GENERIC: propagate-before ( node -- )

GENERIC: propagate-after ( node -- )

GENERIC: annotate-node ( node -- )

GENERIC: propagate-around ( node -- )

GENERIC: propagate-reflinks ( node -- )

GENERIC: propagate-escape ( node -- )

: (propagate) ( nodes -- )
    [ [ compute-copy-equiv ] [ propagate-around ] bi ] each ;

: extract-value-info ( values -- assoc )
    [ dup value-info ] H{ } map>assoc ;

: (annotate-node) ( node values -- )
    extract-value-info >>info drop ; inline

M: node propagate-before drop ;

M: node propagate-after drop ;

M: node annotate-node drop ;

M: node propagate-reflinks drop ;

M: node propagate-escape drop ;

M: node propagate-around
    {
        [ propagate-reflinks ]
        [ propagate-before ]
        [
            ! Runs after before because we need to know whether the word was inlined
            propagate-rw-slots?
            [ propagate-escape ] [ drop ] if
        ]
        [ annotate-node ]
        [ propagate-after ]
    } cleave ;
