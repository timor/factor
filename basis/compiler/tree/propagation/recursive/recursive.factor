! Copyright (C) 2008, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs assocs.extras classes classes.algebra combinators
compiler.tree compiler.tree.combinators compiler.tree.propagation.constraints
compiler.tree.propagation.copy compiler.tree.propagation.escaping
compiler.tree.propagation.info compiler.tree.propagation.info.private compiler.tree.propagation.nodes
compiler.tree.propagation.simple kernel math math.intervals namespaces sequences
sets ;
FROM: sequences.private => array-capacity ;
FROM: namespaces => set ;
IN: compiler.tree.propagation.recursive


! * Virtual counter generalization
! - Treat generalize-counter as a set-slot operation, which performs an update
!   depending on the values present in the respective header merging.
! - Generally speaking, any virtuals that have been freshly allocated inside the
!   loop can only leave the loop via the final phi.  The other case being memory
!   leaks.
! - Loop-allocated virtuals should only be able to re-enter the header for
!   generalization once.  The next iteration, they should have been replaced.
! - Virtuals update after counter-generalization:
!   - Destructive slot update of outside-allocated slot, unique definer
!     { value1(live) value1'(baked) } -> strong-update:
!     value1'(live) = union value1(live), generalized(value1)
!   - Destructive slot update of outside-allocated slot, non-unique definer
!     { value1(live) value2(live) value1'(baked) value2'(baked) }
!     -> weak update.  Same effect as strong update, though.
! - TODO Have to figure out how virtual-virtual generalization plays into this.
!   This may be important for updating virtuals which do not play a part in loop
!   termination condition.
!   - Current strategy: (order unclear...)
!     1. Generalize virtuals based on iteration growth
!     2. Generalize regular values, treating as set-slot, thus also being able to
!        extend virtuals value info.
! - TODO Determine if virtual-virtual growth also has to be accounted for when
!   checking for fixed-point.  Problem: have to ensure that they actually grow in
!   the next iteration!.


! With virtuals:
! - Checking for fixed-point using baked infos.  This means we need to bake the
! infos with the virtual state at their respective call sites.

! For #call-recursive and #return-recursive loops: infos1: latest-input-infos ( in-d in value-infos ),
! infos2: recursive-phi-infos ( out-d in infos>> of #enter-recursive  )
: check-fixed-point ( node infos1 infos2 -- )
    [ value-info<= ] 2all?
    [ drop ] [ label>> f >>fixed-point drop ] if ;

: bake-with ( infos assoc -- infos )
    [ value-infos [ swap suffix ] change [ bake-info ] map ] with-scope ;

: latest-input-infos ( node -- infos )
    in-d>> [ value-info ] map ;

: baked-node-input-infos ( node -- infos )
    propagate-rw-slots?
    [ [ node-input-infos ] [ virtual-infos>> ] bi
      bake-with ]
    [ node-input-infos ] if ;

! Pulls up info from all call sites to set up comparison with the
! beginning-of-loop stack state, which is stored on the input infos of the
! #enter-recursive loop header.
: recursive-stacks ( #enter-recursive -- stacks initial )
    [ label>> calls>> [ node>> baked-node-input-infos ] map flip ]
    [ latest-input-infos ] bi ;

: recursive-virtual-infos ( seq #enter-recursive -- call-site-assocs initial-assoc )
    [ label>> calls>> [ node>> virtual-infos>> extract-keys sift-values ] with map ]
    [ virtual-infos-in>> extract-keys sift-values ] 2bi ;

: counter-class ( interval class -- class' )
    dup fixnum class<= rot array-capacity-interval interval-subset? and
    [ drop array-capacity ] when ;

:: generalize-counter-interval ( interval initial-interval class -- interval' )
    interval class counter-class :> class
    {
        { [ interval initial-interval interval-subset? ] [ initial-interval ] }
        { [ interval empty-interval? ] [ initial-interval ] }
        {
            [ interval initial-interval interval>= t eq? ]
            [ class max-value [a,a] initial-interval interval-union ]
        }
        {
            [ interval initial-interval interval<= t eq? ]
            [ class min-value [a,a] initial-interval interval-union ]
        }
        [ class class-interval ]
    } cond ;

DEFER: generalize-counter
! NOTE: we also update read-only slots here!
: virtuals-to-generalize ( slot-info' initial -- seq )
    [ dup lazy-info? [ values>> ] [ drop f ] if ] bi@
    union members ;

: generalize-lazy-counter-slot ( lazy-info' initial-lazy-info -- info )
    [ [ >info ] bi@ generalize-counter ]
    [ virtuals-to-generalize weak-update ]
    [ nip ] 2tri ;

! Generalizing lazy slots is a no-op, this is done in a separate step.
: generalize-counter-slot ( slot-info' initial -- slot-info )
    2dup [ lazy-info? ] either?
    [ generalize-lazy-counter-slot ]
    [ generalize-counter ] if ;

: generalize-counter ( info' initial -- info )
    2dup [ not ] either? [ drop ] [
        2dup [ class>> null-class? ] either? [ drop ] [
            2dup [ lazy-info? ] either? [
                generalize-lazy-counter-slot
            ] [
                [ clone ] dip
                [
                    [ drop ] [
                        [ [ interval>> ] bi@ ] [ drop class>> ] 2bi
                        generalize-counter-interval
                    ] 2bi >>interval
                ]
                [ [ drop ] [ [ slots>> ] bi@
                             [ generalize-counter ] 2map ] 2bi >>slots ]
                bi
            ] if
        ] if
    ] if ;


PREDICATE: virtual-container-info < value-info-state
    slots>> [ maybe{ lazy-info } instance? ] all? ;

! Generalizing virtuals:
! Each call site and the return node has a virtual-infos assoc.
! Recusive stacks are unified as regular, out-d of #enter-recursive is set to
! the result of counter generalization.  The nested virtuals will all have the
! same values.
! After that, perform the same thing with the virtuals, ensuring that the info
! grows accordingly.

! Takes the recursive call site stack states and the iteration beginning state.
! The call-site states are all merged into a single virtual call site, and then
! extended using the entry state.  The result of that is then stored in the loop
! header out-d value info states and at the out-d infos of the header node.
: unify-recursive-stacks ( stacks initial -- infos )
    over empty? [ nip ] [
        [
            [ value-infos-union ] dip
            [ generalize-counter ] keep
            value-info-union
            ! thaw-info Doesn't seem to be necessary
            propagate-rw-slots? [ virtual-container-info check-instance ] when
        ] 2map
    ] if ;

: unify-recursive-virtuals ( call-site-assocs initial-assoc -- assoc )
    [ [ value-info-union ] assoc-collapse ] dip
    [ [ generalize-counter ] assoc-merge! ] keep
    [ value-info-union ] assoc-merge! ;

: propagate-recursive-phi ( #enter-recursive -- )
    [ recursive-stacks unify-recursive-stacks ] keep
    out-d>> set-value-infos ;

: changed-virtuals ( -- seq )
    inner-values get last
    virtual-values get intersect members ;

: propagate-recursive-phi-virtuals ( #enter-recursive -- )
    changed-virtuals swap recursive-virtual-infos
    unify-recursive-virtuals
    [ swap set-inner-value-info ] assoc-each ;


! Current state:
! By not baking the info to the annotated nodes, initial state for comparison is
! updated as well.  Thus, all termination checks and counter-growers see the
! same stuff.  Correct behavior:
! - Compare initial state at loop header with propagated state at call/return
! site
! - Keep strong updates by not literalizing in-between via baking
! - Interval generalization updates iteration state correctly
! - Last updated iteration state is kept

SYMBOL: recursion-limit
recursion-limit [ 200 ] initialize
SYMBOL: sentinel

: baked-virtual-infos ( -- assoc )
    H{ } clone
    virtual-values get members
    [ [ value-info bake-info ] keep pick set-at ] each ;

: capture-initial-virtuals ( #enter-recursive -- )
    baked-virtual-infos >>virtual-infos-in drop ;

: capture-iteration-virtuals ( #enter-recursive -- )
    baked-virtual-infos >>virtual-infos-out drop ;

: capture-call-site-virtuals ( node -- )
    baked-virtual-infos >>virtual-infos drop ;

! TODO: check that inner-values state is correct after return

! Merge the ones that have been changed in the loop body upwards
: include-changed-virtuals ( -- )
    propagate-rw-slots? [
        inner-values get
        unclip-last swap
        [ 1array ]
        [ unclip-last swapd union suffix ] if-empty
        inner-values set
    ] when ;

M: #recursive propagate-around ( #recursive -- )
    constraints [ H{ } clone suffix ] change
    inner-values [ V{ } clone suffix ] change
    dup child>> first capture-initial-virtuals
    [
        sentinel counter recursion-limit get > [ "recursion limit" throw ] when
        constraints [ but-last H{ } clone suffix ] change

        child>>
        {
            [ first compute-copy-equiv ]
            [ first propagate-recursive-phi-virtuals ]
            [ first propagate-recursive-phi ]
            [ (propagate) ]
        } cleave
    ] until-fixed-point
    include-changed-virtuals
    ;

: recursive-phi-infos ( node -- infos )
    label>> enter-recursive>> node-output-infos ;

: generalize-return-interval ( info -- info' )
    dup [ literal?>> ] [ class>> null-class? ] bi or
    [ clone dup class>> class-interval >>interval ] unless ;

: generalize-return ( infos -- infos' )
    [ generalize-return-interval ] map ;

: return-infos ( node -- infos )
    label>> return>> node-input-infos generalize-return ;

: save-return-infos ( node infos -- )
    swap out-d>> set-value-infos ;

: unless-loop ( node quot -- )
    [ dup label>> loop?>> [ drop ] ] dip if ; inline

: baked-recursive-phi-infos ( node -- infos )
    propagate-rw-slots?
    [ label>> enter-recursive>>
      [ node-output-infos ] [ virtual-infos-out>> ] bi
      bake-with ]
    [ recursive-phi-infos ] if ;

! TODO: non-loops
M: #call-recursive propagate-before ( #call-recursive -- )
    [
        [ ] [ latest-input-infos ] [ baked-recursive-phi-infos ] tri
        check-fixed-point
    ]
    [
        [
            [ ] [ return-infos ] [ node-output-infos ] tri
            [ check-fixed-point ] [ drop save-return-infos ] 3bi
        ] unless-loop
    ] bi ;

M: #call-recursive annotate-node
    dup capture-call-site-virtuals
    dup [ in-d>> ] [ out-d>> ] bi append (annotate-node) ;

M: #enter-recursive annotate-node
    dup capture-iteration-virtuals
    dup out-d>> (annotate-node) ;

M: #return-recursive propagate-before ( #return-recursive -- )
    [
        [ ] [ latest-input-infos ] [ baked-node-input-infos ] tri
        check-fixed-point
    ] unless-loop ;

M: #return-recursive annotate-node
    dup capture-call-site-virtuals
    dup in-d>> (annotate-node) ;
