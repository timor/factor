USING: accessors arrays byte-arrays classes combinators
combinators.short-circuit compiler.tree.propagation.info
compiler.tree.propagation.nodes compiler.tree.propagation.special-nodes kernel
math math.intervals sequences strings ;

IN: compiler.tree.propagation.set-slots

! * Set slot propagation
! Strong or weak, depending on virtual definer uniqueness.
: update-info-slot ( new-info container-info n -- )
    swap slots>> nth lazy-info check-instance
    update-lazy-info ;

! ** Tuple set slot call
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

M: tuple-set-slot-call propagate-after
    [ call-next-method ] keep
    propagate-rw-slots?
    [ propagate-tuple-set-slot-infos ] [ drop ] if ;

! ** Array/Fixed-length set-slot call
! Concerns strings, byte arrays and arrays.  If the length is one, destructive
! updates may be strong, depending on slot uniqueness.  If it is longer, it is
! treated as summary allocation, and only weak updates are tracked.

: ensure-obj-slots ( value -- )
    dup value-info dup summary-slot>>
    [ 2drop ]
    [ clone add-summary-slot
      swap set-value-info
    ] if ;

! Modify the virtual representing the contents to include the given element info.
: include-summary-slot-content ( element-info array-info -- )
    summary-slot>> lazy-info check-instance
    update-lazy-info-weak ;

: update-summary-slot ( new-info conainer-info -- )
    summary-slot>> lazy-info check-instance
    update-lazy-info ;

! set-slot ( value obj n -- )
: propagate-sequence-set-slot-infos ( #call strong? -- )
    swap in-d>> first2 dup ensure-obj-slots
    [ value-info ] bi@
    rot [ update-summary-slot ]
    [ include-summary-slot-content ] if ;

GENERIC: propagate-set-slot ( #call -- )
M: box-set-slot-call propagate-set-slot
    t propagate-sequence-set-slot-infos ;
M: sequence-set-slot-call propagate-set-slot
    f propagate-sequence-set-slot-infos ;
M: string-aux-writer propagate-set-slot
    propagate-tuple-set-slot-infos ;

M: sequence-set-slot-call propagate-after
    [ call-next-method ] keep
    propagate-rw-slots?
    [ propagate-set-slot ] [ drop ] if ;

! set-slot calls where either the slot is unknown, or the container has no slots
! specified.  This concerns set-nth calls with unknown index, and sequences that
! have not been allocated locally.

M: non-literal-sequence-set-slot-call propagate-after
    [ call-next-method ] keep
    propagate-rw-slots?
    [ f propagate-sequence-set-slot-infos ]
    [ drop ] if ;

! ** Resize-array
! Resize-array must be assumed to set the length slot if the length is smaller
! or equal than the current, but will allocate a new array otherwise.

: length-info= ( info info -- ? )
    [ interval>> singleton-interval>point ] bi@
    { [ and ] [ = ] } 2&& ;

: length-info<= ( info info -- ? )
    [ interval>> ] bi@ interval> not ;

PREDICATE: known-resize-sequence-call < resize-sequence-call
    in-d>> second value-info slots>> ;
PREDICATE: unknown-resize-sequence-call < resize-sequence-call
    known-resize-sequence-call? not ;
PREDICATE: shrinking-resize-sequence-call < known-resize-sequence-call
    in-d>> first2 [ value-info ] bi@ slots>> first length-info<= ;
PREDICATE: nop-resize-sequence-call < shrinking-resize-sequence-call
    in-d>> first2 [ value-info ] bi@ slots>> first length-info= ;
PREDICATE: growing-resize-sequence-call < known-resize-sequence-call
    shrinking-resize-sequence-call? not ;

! If array is newly allocated, resulting storage will not share slots
: allocates-larger-sequence ( n-info array-info -- out-info )
    cloned-value-info
    ! Should always be a strong update
    [ 0 update-info-slot ] keep ;

: set-length-sequence ( n-info array-info -- out-info )
    [ 0 update-info-slot ] keep
    clone
    f >>literal
    f >>literal? ;

! For a an unknown allocation, we don't modify the input info.
: resize-unknown-sequence ( n-info array-val -- out-info )
    swap object-info swap array <rw-sequence-info>
    swap drop ;

: default-element-info ( class -- info )
    { { string [ 0 ] }
      { byte-array [ 0 ] }
      { array [ f ] }
    } case <literal-info> ;

GENERIC: propagate-resize-sequence-output-infos* ( #call -- infos )
GENERIC: propagate-resize-array-input-infos ( #call -- )
M: unknown-resize-sequence-call propagate-resize-sequence-output-infos*
    in-d>> first2 [ value-info ] bi@ resize-unknown-sequence ;
! TODO: inline as [ ]
M: nop-resize-sequence-call propagate-resize-sequence-output-infos*
    in-d>> second value-info ;
M: shrinking-resize-sequence-call propagate-resize-sequence-output-infos*
    in-d>> first2 [ value-info ] bi@ set-length-sequence ;
M: growing-resize-sequence-call propagate-resize-sequence-output-infos*
    in-d>> first2 [ value-info ] bi@ allocates-larger-sequence
    [ class>> default-element-info ] keep
    [ include-summary-slot-content ] keep ;

! resize-array ( n array -- array )
: propagate-resize-sequence-output-infos ( #call -- )
    [ propagate-resize-sequence-output-infos* ]
    [ out-d>> first ] bi set-value-info ;

M: resize-sequence-call propagate-before
    [ call-next-method ] keep
    propagate-rw-slots?
    [ propagate-resize-sequence-output-infos ] [ drop ] if ;

M: shrinking-resize-sequence-call propagate-around
    propagate-rw-slots? [
        {
            [ dup in-d>> (annotate-node) ]
            [ propagate-before ]
            [ in-d>> second
              [ value-info clone f >>literal f >>literal? ]
              [ set-value-info ] bi ]
            [ dup out-d>> (annotate-node-also) ]
            [ propagate-after ]
        } cleave
    ]
    [ call-next-method ] if ;

! TODO resize-byte-array
