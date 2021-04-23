USING: accessors classes.algebra classes.tuple classes.tuple.private
combinators.short-circuit compiler.tree compiler.tree.propagation.info kernel
sequences slots.private words ;

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

! * Reflink propagation

! ** Predicate hierarchy for class dispatch (what a mess...)
PREDICATE: flushable-call < #call word>> flushable? ;
PREDICATE: slot-call < flushable-call word>> \ slot eq? ;
PREDICATE: literal-slot-call < slot-call
    in-d>> second value-info { [ literal?>> ] [ literal>> 0 = not ] } 1&& ; ! Exclude length slot calls

PREDICATE: rw-slot-call < literal-slot-call
    in-d>> first2 [ value-info class>> ] [ value-info literal>> ] bi* swap read-only-slot? not ;
PREDICATE: tuple-boa-call < flushable-call word>> \ <tuple-boa> eq? ;

PREDICATE: non-flushable-call < #call flushable-call? not ;
PREDICATE: inlined-call < non-flushable-call body>> >boolean ;
UNION: non-escaping-call flushable-call inlined-call ;

PREDICATE: set-slot-call < non-flushable-call word>> \ set-slot eq? ;
PREDICATE: literal-set-slot-call < set-slot-call in-d>> third value-info literal?>> ;
PREDICATE: tuple-set-slot-call < literal-set-slot-call in-d>> second value-info class>> tuple class<= ;

PREDICATE: tuple-push < #push literal>> tuple? ;
PREDICATE: mutable-tuple-push < tuple-push literal>> immutable-tuple-class? not ;
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
