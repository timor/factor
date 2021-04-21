USING: accessors compiler.tree compiler.tree.propagation.escaping
compiler.tree.propagation.info compiler.tree.propagation.nodes
compiler.tree.propagation.reflinks kernel math sequences sets ;

IN: compiler.tree.propagation.slot-refs

! Find ourselves in other tuples slots.
! Return whether we are still referenced, and check for a strong definition
! relation by checking whether our slot-refs are a superset of the target.  If
! not, other definitions have been involved, thus only weak update is possible.

: back-ref-slot ( info slot-ref -- strong? current? )
    [ slot-refs>> ] [ dereference slot-refs>> ] bi*
    [ swap subset? ] [ intersects? ] 2bi ; inline
    ! dup dereference slot-refs>>
    ! [ in? ]
    ! [ length 1 = ] bi swap ;

! Must ripple through
: notice-slot-changed ( info -- )
    dup slot-refs>> members [
        2dup back-ref-slot
        [  [ [ strong-update ]
             [ weak-update ] if ] keepd
           parent-info notice-slot-changed
        ]
        [ 3drop ] if
    ] with each ;

! set-slot ( value obj n -- )
M: tuple-set-slot-call propagate-slot-refs
    in-d>> first3
    value-info literal>> set-slot-ref
    notice-slot-changed
    ;

M: tuple-boa-call propagate-slot-refs
    [ out-d>> first ]
    [ in-d>> but-last ] bi
    [ 2 + set-slot-ref drop ] with each-index ;

! TODO: deliteralize

! * Escaping slot-refs
M: #introduce propagate-escape
    out-d>> [ value-escapes ] each ;
M: non-escaping-call propagate-escape drop ;
M: #call propagate-escape
    [ in-d>> [ object-escapes ] each ]
    [ out-d>> [ value-escapes ] each ] bi ;
