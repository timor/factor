USING: accessors assocs classes.algebra classes.tuple.private
combinators.short-circuit compiler.tree compiler.tree.propagation.copy
compiler.tree.propagation.escaping compiler.tree.propagation.info
compiler.tree.propagation.nodes kernel math namespaces sequences sets
slots.private words ;

IN: compiler.tree.propagation.reflinks

FROM: namespaces => set ;

! ** Reference tracking and Escape analysis
! Each value has a backref>> slot, which contains a link-ref instance.  Unlike
! copy propagatin, this link-ref tracks which values could directly have defined
! this value, and vice versa, based on slot dereferencing.  This link-ref can be
! used to track equivalence in the escaping-values disjoint set state.  Note
! that this state is kept per branch, so an escaping value in one branch will
! not affect the other until branch return.  For each value that (as well as
! for each reference change), the changed infos are collected in
! inner-slot-ref-values.  The infos stored therein are merged upon branch
! return.  While regular value passing info is merged at the phi node, these
! virtual values are not necessarily visible there.  Upon branch return, the
! link-refs of the values stored in inner-slot-ref-values are used to update the
! escaping-values state in parent scope
! TODO: handle #recursive

! TODO: equating to value info merge!
! Assert that all definers of this value have same escape status
! Assert that all values defined by this value have same escape status
! Assert that values defind by this value, and values this value defines, have
! same escape status

: merge-link-refs ( value-info -- )
    backref>> [ defined-by>> ] [ defines>> ] bi
    [ [ equate-all-values ] bi@ ]
    [ [ ?first ] bi@ equate-values ] 2bi ;

SYMBOL: allocations
: record-allocation ( value -- )
    allocations get [ adjoin ] [ drop ] if* ;

PREDICATE: tuple-boa-call < #call word>> \ <tuple-boa> eq? ;
PREDICATE: slot-call < #call word>> \ slot eq? ;
PREDICATE: set-slot-call < #call word>> \ set-slot eq? ;
PREDICATE: literal-set-slot-call < set-slot-call in-d>> third value-info literal?>> ;
PREDICATE: tuple-set-slot-call < literal-set-slot-call in-d>> second value-info class>> tuple class<= ;
PREDICATE: tuple-push < #push literal>> tuple? ;
PREDICATE: sequence-push < #push literal>> fixed-length? ;
UNION: storage-class tuple fixed-length ;

! Establishes that defined-by defines defined value
! 1. Add defined value to defined-by-s defines set
! Equate them in the set of escaping values.

! : link-values ( definer defined -- )
!     [ equate-values ]
!     [ [ record-inner-value ] bi@ ]
!     [  ]
!     2dup equate-values
!     [ resolve-copy [ record-slot-ref-value ] keep ] bi@
!     2dup <reflink-info>
!     '[ _ swap refine-value-info ] bi@ ;

! TODO: establish definer link on set-slot call

! slot ( obj m -- value )
! TODO TBR
M: slot-call propagate-reflinks
    ! drop ;
    [ in-d>> first ]
    [ out-d>> first ] bi add-value-definition ;

!
! M: tuple-set-slot-call propagate-reflinks


: object-escapes? ( value -- ? )
    resolve-copy value-escapes? ;

! Recursive!
: object-escapes ( value -- )
    resolve-copy dup value-escapes?
    [ drop ]                    ! Break recursion
    [
        [ value-escapes ]
        [ value-info backref>> defines>> [ object-escapes ] each ]
        [ invalidate-slots-info ] tri
    ] if ;

! ! Check if this value has been defined by something that could have escaped
: value-info-escapes? ( info -- ? )
    backref>> defined-by>> object-escapes? ;

M: tuple-boa-call propagate-reflinks
    out-d>> first record-allocation ;

M: tuple-push propagate-reflinks
    out-d>> first record-allocation ;

M: sequence-push propagate-reflinks
    out-d>> first record-allocation ;

M: #declare propagate-reflinks
    declaration>> [ storage-class? [ record-allocation ] [ drop ] if ] assoc-each ;

! ** Escape handling

! FIXME: if we had QUALIFY, we could inherit from slot-call
PREDICATE: literal-slot-call < #call
    { [ word>> \ slot eq? ]
      [ in-d>> second value-info { [ literal?>> ] [ literal>> 0 = not ] } 1&& ]
    } 1&& ; ! Exclude length slot calls

PREDICATE: rw-slot-call < literal-slot-call
    in-d>> first2 [ value-info class>> ] [ value-info literal>> ] bi* swap read-only-slot? not ;

PREDICATE: flushable-call < #call
    { [ word>> flushable? ] [ rw-slot-call? not ] } 1&& ;
PREDICATE: inlined-call < #call body>> >boolean ;

UNION: non-escaping-call flushable-call inlined-call tuple-set-slot-call ;

! TODO: arrays

M: #introduce propagate-escape
    out-d>> [ value-escapes ] each ;
M: non-escaping-call propagate-escape drop ;
M: #call propagate-escape
    [ in-d>> [ object-escapes ] each ]
    [ out-d>> [ value-escapes ] each ] bi ;

! ** Slot access refinement

! ! TODO: remove regular slot access code
! : mask-rw-slot-access ( slot info -- info'/f )
!     2dup
!     { [ class>> read-only-slot? ]
!       ! [ { [ 2drop propagate-rw-slots? ]
!       !     [ valid-rw-slot-access? ] } 2&&
!       ! ]
!       [ 2drop propagate-rw-slots? ]
!     } 2||
!     [ [ 1 - ] [ slots>> ] bi* ?nth ]
!     [ 2drop f ] if ;

! ! Step 1: non-literal tuples
! : value-info-slot-mask-rw ( slot info -- info' )
!     {
!         { [ over 0 = ] [ 2drop fixnum <class-info> ] } ! This is a length slot, why no deref?
!         { [ dup literal?>> propagate-rw-slots? and ] [ mask-rw-slot-access ] }
!         { [ dup literal?>> ] [ literal>> literal-info-slot ] }
!         [ mask-rw-slot-access ]
!     } cond [ object-info ] unless* ;

! Situation: output-value-infos has run.  Now repeat.  For now, only if this is
! an rw-slot access

! slot ( obj m -- value )
! TODO technically not part of escape protocol
M: rw-slot-call propagate-escape
    [ in-d>> second value-info literal>> ]
    [ in-d>> first value-info
      [ 1 - ] [ slots>> ] bi* ?nth
    ]
    [ out-d>> first
      over [ refine-value-info ] [ 2drop ] if
    ] tri ;
