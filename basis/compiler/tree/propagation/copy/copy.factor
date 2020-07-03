! Copyright (C) 2008 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors assocs compiler.tree compiler.tree.def-use
compiler.utilities grouping kernel namespaces sequences sets
stack-checker.branches ;
IN: compiler.tree.propagation.copy

SYMBOL: copies

! Follows back the COPY value through the copies assoc stack, and returns the
! original "definer".  This is used quite often, especially before "modifying"
! value information, usually using `refine-value-info`, which also writes back
! its information to the source copy.  That means that any "use" of a value's
! info would also have to resolve the copies before accessing the information.
! Just checked.  in compiler.tree.propagation.info, the `value-info` access does
! exactly that.  Moral of the story: Never access value infos locally on a node.
! Currently, copies are created on #renaming nodes, and on the #phi dominators
! which always follow #branch nodes (I think).

! NOTE: resolve-copy never leaves its scope.  E.g. for branches, the top
! assoc-stack entry is cloned, so that each branch gets its own "instance" of
! these assocs, and can modify any value associations independently from the
! other branches or any parent scope.  On branch return/inlining return, a #copy
! node is inserted which captures the last value-info states for the code
! block's output values.

! `compute-copy-equiv` is called before propagation at the nodes

: resolve-copy ( copy -- val ) copies get compress-path ;

: resolve-copies ( copies -- vals )
    copies get [ compress-path ] curry map ;

: is-copy-of ( val copy -- ) copies get set-at ;

: are-copies-of ( vals copies -- ) [ is-copy-of ] 2each ;

: introduce-value ( val -- ) copies get conjoin ;

: introduce-values ( vals -- )
    copies get [ conjoin ] curry each ;

GENERIC: compute-copy-equiv* ( node -- )

M: #renaming compute-copy-equiv* inputs/outputs are-copies-of ;

: compute-phi-equiv ( inputs outputs -- )
    [
        swap remove-bottom resolve-copies
        dup [ f ] [ all-equal? ] if-empty
        [ first swap is-copy-of ] [ 2drop ] if
    ] 2each ;

M: #phi compute-copy-equiv*
    [ phi-in-d>> flip ] [ out-d>> ] bi compute-phi-equiv ;

M: node compute-copy-equiv* drop ;

: compute-copy-equiv ( node -- )
    [ node-defs-values introduce-values ]
    [ compute-copy-equiv* ]
    bi ;
