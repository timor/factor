! Copyright (C) 2008, 2009 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs classes.algebra combinators
combinators.short-circuit compiler.tree compiler.tree.builder
compiler.tree.normalization compiler.tree.propagation.constraints
compiler.tree.propagation.copy compiler.tree.propagation.info
compiler.tree.propagation.mutually-recursive.branch-overrides
compiler.tree.propagation.mutually-recursive.interface
compiler.tree.propagation.mutually-recursive.pruning
compiler.tree.propagation.nodes compiler.tree.propagation.simple
compiler.tree.recursive generic generic.math generic.single generic.standard io
kernel locals math math.partial-dispatch namespaces quotations sequences words ;
IN: compiler.tree.propagation.inlining

: splicing-call ( #call word -- nodes )
    [ [ in-d>> ] [ out-d>> ] bi ] dip <#call> 1array ;

: open-code-#call ( #call word/quot -- nodes/f )
    [ [ in-d>> ] [ out-d>> ] bi ] dip build-sub-tree ;

: splicing-body ( #call quot/word -- nodes/f )
    open-code-#call dup [ analyze-recursive normalize ] when ;

! Dispatch elimination
: undo-inlining ( #call -- ? )
    f >>method f >>body f >>class drop f ;

: propagate-body ( #call -- ? )
    body>> (propagate) t ;

GENERIC: splicing-nodes ( #call word/quot -- nodes/f )

M: word splicing-nodes splicing-call ;

M: callable splicing-nodes splicing-body ;

: eliminate-dispatch ( #call class/f word/quot/f -- ? )
    dup [
        [ >>class ] dip
        over method>> over = [ drop propagate-body ] [
            2dup splicing-nodes dup [
                [ >>method ] [ >>body ] bi* propagate-body
            ] [ 2drop undo-inlining ] if
        ] if
    ] [ 2drop undo-inlining ] if ;

: inlining-standard-method ( #call word -- class/f method/f )
    dup "methods" word-prop assoc-empty? [ 2drop f f ] [
        2dup [ in-d>> length ] [ dispatch# ] bi* <= [ 2drop f f ] [
            [ in-d>> <reversed> ] [ [ dispatch# ] keep ] bi*
            [ swap nth value-info class>> dup ] dip
            method-for-class
        ] if
    ] if ;

: inline-standard-method ( #call word -- ? )
    dupd inlining-standard-method eliminate-dispatch ;

: normalize-math-class ( class -- class' )
    {
        null
        fixnum bignum integer
        ratio rational
        float real
        complex number
        object
    } [ class<= ] with find nip ;

: inlining-math-method ( #call word -- class/f quot/f )
    swap in-d>>
    first2 [ value-info class>> normalize-math-class ] bi@
    3dup math-both-known?
    [ math-method* ] [ 3drop f ] if
    number swap ;

: inline-math-method ( #call word -- ? )
    dupd inlining-math-method eliminate-dispatch ;

! Method body inlining
SYMBOL: history

: already-inlined? ( obj -- ? ) history get member-eq? ;

: add-to-history ( obj -- ) history [ swap suffix ] change ;

:: inline-word ( #call word -- ? )
    word already-inlined? [ f ] [
        #call word splicing-body [
            word add-to-history
            #call body<<
            #call propagate-body
        ] [ f ] if*
    ] if ;

: always-inline-word? ( word -- ? )
    { curry compose } member-eq? ;

: never-inline-word? ( word -- ? )
    { [ deferred? ] [ "default" word-prop ] [ \ call eq? ] } 1|| ;

: custom-inlining? ( word -- quot/f )
    "custom-inlining" word-prop ;

: inline-custom ( #call word -- ? )
    [ dup ] [ custom-inlining? ] bi*
    call( #call -- word/quot/f )
    object swap eliminate-dispatch ;

! Perform propagation on nodes of inlined words.  Separates scope to ensure that
! duplicate value names are handled correctly.
:: propagate-inline ( call nodes -- infos ret-values )
    call in-d>> [ value-info ] map :> input-info
    call out-d>> :> out-values
    nodes unclip :> ( nodes' intro )
    call in-d>> intro out-d>> <#copy> nodes' swap prefix :> nodes'
    [
        H{ } clone copies set
        value-infos [ H{ } clone suffix ] change
        constraints [ H{ } clone suffix ] change
        input-info nodes' first in-d>> set-value-infos
        nodes' (propagate)
        nodes' last [ in-d>> ] [ node-input-infos ] bi
    ] with-scope
    [ out-values set-value-infos ] keep
    swap
    ;

! Interface to propagation.mutually-recursive
! Inline the pruned body and perform propagation
! Undo inlining afterwards
: inline-recursive-call ( #call word -- ? )
    name>> "Inlining recursive call to " write print flush
    H{ } clone rec-return-infos get push
    [
        current-body get over swap pruned-recursion-inline-body
        [ current-body set ]
        [ propagate-inline ] bi

        ! [ propagate-body ] keep

    ] with-branch-overrides
    rec-return-infos get pop drop       ! Throw away inner recursions
    push-rec-return-infos
    t
    ;

! For inlining all the calls in the cycle, it makes sense to cache the splicing
! bodies.  This cache should have the same lifetime as the compilation unit
! TODO ensure that there are no problems using cached expansions because of
! value duplicates.  If there are, use propagate-inline as above.
: nested-propagation-body ( #call word -- nodes )
    dup "propagation-body" word-prop
    [ 2nip ]
    [ [ splicing-body ] keep swap
      [ "propagation-body" set-word-prop ] keep ]
    if* ;

! Inline the non-pruned body and perform propagation
! Undo inlining afterwards
: inline-nested-compilation ( #call word -- ? )
    dupd nested-propagation-body >>body
    [ propagate-body ] keep
    f swap body<< ;


: (do-inlining) ( #call word -- ? )
    {
        { [ dup never-inline-word? ] [ 2drop f ] }
        { [ dup always-inline-word? ] [ inline-word ] }
        { [ dup standard-generic? ] [ inline-standard-method ] }
        { [ dup math-generic? ] [ inline-math-method ] }
        { [ dup inline? ] [ inline-word ] }
        { [ over recursive-inline? ] [ inline-recursive-call ] }
        { [ over mutual-recursive-inline? ] [ inline-nested-compilation ] }
        [ 2drop f ]
    } cond ;

: do-inlining ( #call word -- ? )
    [
        dup custom-inlining? [ 2dup inline-custom ] [ f ] if
        [ 2drop t ] [ (do-inlining) ] if
    ] with-scope ;
