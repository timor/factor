USING: accessors arrays classes combinators.short-circuit
compiler.tree.propagation.info compiler.tree.propagation.nodes
compiler.tree.propagation.special-nodes kernel math math.intervals sequences ;

IN: compiler.tree.propagation.set-slots

! * Set slot propagation

! FIXME: perform input info manipulation after annotation!!!
! At least for resize-array

! Fetch the correct slot from obj's info state.  We expect this to be a lazy
! slot entry.
: propagate-tuple-set-slot-infos ( #call -- )
    in-d>> first3
    [let :> ( value-val obj-val n-val )
     value-val value-info :> new-info
     n-val value-info literal>> :> slot-num
     obj-val value-info slots>> slot-num 1 - swap ?nth :> slot-info
     slot-info [
         lazy-info check-instance
         new-info swap update-lazy-info
     ] when*
    ] ;

M: tuple-set-slot-call propagate-before
    [ call-next-method ] keep
    propagate-rw-slots?
    [ propagate-tuple-set-slot-infos ] [ drop ] if ;

! Resize-array must be assumed to set the length slot if the length is smaller
! or equal than the current, but will allocate a new array otherwise.

: length-info= ( info info -- ? )
    [ interval>> singleton-interval>point ] bi@
    { [ and ] [ = ] } 2&& ;

: length-info<= ( info info -- ? )
    [ interval>> ] bi@ interval> not ;

PREDICATE: known-resize-array-call < resize-array-call
    in-d>> second value-info slots>> ;
PREDICATE: unknown-resize-array-call < resize-array-call
    known-resize-array-call? not ;
PREDICATE: shrinking-resize-array-call < known-resize-array-call
    in-d>> first2 [ value-info ] bi@ slots>> first length-info<= ;
PREDICATE: nop-resize-array-call < shrinking-resize-array-call
    in-d>> first2 [ value-info ] bi@ slots>> first length-info= ;
PREDICATE: growing-resize-array-call < known-resize-array-call
    shrinking-resize-array-call? not ;

! Strong or weak, depending on virtual definer uniqueness.
: update-info-slot ( new-info container-info slot-num -- )
    swap slots>> nth lazy-info check-instance
    update-lazy-info ;

! If array is newly allocated, resulting storage will not share slots
: allocates-larger-array ( n-info array-info -- out-info )
    cloned-value-info
    ! Should always be a strong update
    [ 0 update-info-slot ] keep ;

! Modify the virtual representing the contents to include the default element
! after resize.  For arrays: f, for byte-arrays: 0.
: include-default-slot-content ( array-info element-info -- array-info )
    [ swap slots>> last lazy-info check-instance
      update-lazy-info-weak ] keepd ;

: set-length-array ( n-info array-info -- out-info )
    [ 0 update-info-slot ] keep ;

! For a an unknown allocation, we modify the input info!
: resize-unknown-array ( n-info array-val -- out-info )
    swap object-info swap array <rw-sequence-info>
    [ swap set-value-info ] keep ;

GENERIC: propagate-resize-array-output-infos* ( #call -- infos )
GENERIC: propagate-resize-array-input-infos ( #call -- )
M: unknown-resize-array-call propagate-resize-array-output-infos*
    in-d>> first2 [ value-info ] bi@ resize-unknown-array ;
M: nop-resize-array-call propagate-resize-array-output-infos*
    in-d>> second value-info ;
M: shrinking-resize-array-call propagate-resize-array-output-infos*
    in-d>> first2 [ value-info ] bi@ set-length-array ;
M: growing-resize-array-call propagate-resize-array-output-infos*
    in-d>> first2 [ value-info ] bi@ allocates-larger-array
    f <literal-info> include-default-slot-content ;

! resize-array ( n array -- array )
: propagate-resize-array-output-infos ( #call -- )
    [ propagate-resize-array-output-infos* ]
    [ out-d>> first ] bi set-value-info ;

M: resize-array-call propagate-before
    [ call-next-method ] keep
    propagate-rw-slots?
    [ propagate-resize-array-output-infos ] [ drop ] if ;

! M: resize-array-call propagate-after
!     [ call-next-method ] keep
!     propagate-rw-slots?
!     [ propagate- ]
!     [  ]
