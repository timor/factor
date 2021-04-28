USING: accessors classes compiler.tree.propagation.info
compiler.tree.propagation.nodes compiler.tree.propagation.special-nodes kernel
math sequences sets ;

IN: compiler.tree.propagation.set-slots

! * Set slot propagation


! Fetch the correct slot from obj's info state.  We expect this to be a lazy
! slot entry.
: propagate-tuple-set-slot-infos ( #call -- )
    in-d>> first3
    [let :> ( value-val obj-val n-val )
     value-val value-info :> new-info
     n-val value-info literal>> :> slot-num
     obj-val value-info slots>> slot-num 1 - swap ?nth :> slot-info
     slot-info [ lazy-info check-instance
     values>> members :> virtual-values
     virtual-values length 1 = [
         ! Strong update
         new-info virtual-values first strong-update
     ] [
         ! Weak update
         new-info virtual-values weak-update
     ] if ] when*
    ] ;

M: tuple-set-slot-call propagate-before
    [ call-next-method ] keep
    propagate-rw-slots?
    [ propagate-tuple-set-slot-infos ] [ drop ] if ;
