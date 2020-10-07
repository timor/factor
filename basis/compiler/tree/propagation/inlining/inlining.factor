! Copyright (C) 2008, 2009 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs classes.algebra combinators
combinators.short-circuit compiler.messages compiler.tree compiler.tree.builder
compiler.tree.builder.private compiler.tree.normalization
compiler.tree.propagation.info compiler.tree.propagation.nodes
compiler.tree.recursive compiler.utilities continuations generic generic.math
generic.single generic.standard kernel locals math math.intervals
math.partial-dispatch namespaces quotations sequences stack-checker.dependencies
stack-checker.errors words ;
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

! Main point where inlining of generic dispatch during propagation is performed
! - Check if there are any methods
! - Check if the call site has enough inputs to contain the argument to dispatch
!   on (can there be a non-error case otherwise?)
! - If all of that applies, extract the corresponding input info and feed it
!   into method-for-class, which will either return a specific method or f
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


! An assoc storing cached inlined-infos for different value-info inputs for each word

: word-inline-infos-cache ( word -- assoc )
    dup "inline-propagation-infos" word-prop
    [ nip ] [ H{ } clone [ "inline-propagation-infos" set-word-prop ] keep ] if* ;

: convex-input-info ( value-info -- value-info )
    dup interval>> special-interval?
    [ class>> <class-info> ] unless
    dup slots>> [
        [ clone ] dip
        [ dup [ convex-input-info ] when ] map
        >>slots
    ] when* ;
    ! dup literal?>> [ class>> <class-info> ] when ;

: inline-signature ( #call -- obj )
    in-d>> [ value-info convex-input-info ] map ;

: deliteralize-infos ( #call infos -- infos )
    swap word>> foldable?
    [ [ f >>literal? f >>literal? ] map ] unless ;

: trivial-infos? ( infos -- ? )
    [ object-info = ] all? ;

: record-inline-propagation ( #call infos -- )
    trivial-infos? [ drop ] [ word>> +definition+ depends-on ] if ;

SINGLETON: +inline-recursion+
SYMBOL: signature-trace

! TODO: can this be memoized? We could also annotate the word...
: inline-propagation-body ( #call -- nodes/f )
    [ [ in-d>> ] [ word>> ] bi
      build-tree-with ] curry [ inference-error? ] ignore-error/f
    dup
    { [ length 2 < ] [ penultimate #terminate? ] } 1||
    [ drop f ] [ analyze-recursive normalize ] if ;

: cached-inline-propagation-body ( #call -- nodes/f )
    [ word>> ] keep over "inline-body" word-prop
    [ 2nip ]
    [ inline-propagation-body [ "inline-body" set-word-prop ] keep ] if* ;


: propagate-body-for-infos ( #call infos -- infos/f )
    over cached-inline-propagation-body
    [ [
                value-infos [ H{ } clone suffix ] change
                [ [ in-d>> ] dip swap [ set-value-info ] 2each ] dip
                [ (propagate) ] keep last in-d>> [ value-info ] map
            ] with-scope
    ] [ 2drop f ] if*
    ;

: splicing-class-infos ( #call input-infos -- infos/f )
    over word>> name>> "--- Propagating nodes for infos: " prepend compiler-message
    dupd propagate-body-for-infos
    [ dupd deliteralize-infos
      [ record-inline-propagation ] keep
    ] [ drop f ] if* ;

:: cached-inline-propagation-infos ( #call word -- infos/f )
    #call inline-signature :> sig
    word word-inline-infos-cache :> info-cache
    word sig 2array signature-trace get member?
    [ +inline-recursion+ ]
    [
        sig info-cache at
        [ signature-trace [ word sig 2array suffix ] change
        #call sig splicing-class-infos ] unless*
        dup sig info-cache set-at
    ] if ;
    ! sig info-cache at
    ! [ +inline-recursion+ sig info-cache set-at
    !   #call sig splicing-class-infos
    !   [ sig info-cache set-at ] keep
    ! ] unless* dup +inline-recursion+? [ drop f ] when ;

! NOTE: We don't propagate through generic dispatches.  An optimization could be
! to determine whether the input is a proper subset of the generic's method
! definers, and compile in the actual dispatch.
: inline-propagation-infos ( #call word -- infos/f )
    2dup { [ nip primitive? ]
           [ nip generic? ]
           [ nip never-inline-word? ]
           [ nip custom-inlining? ]
           [ drop out-d>> empty? ] } 2||
    [ 2drop f ]
    [ cached-inline-propagation-infos
      dup +inline-recursion+? [ drop f ] when
    ] if ;

: (do-inlining) ( #call word -- ? )
    {
        { [ dup never-inline-word? ] [ 2drop f ] }
        { [ dup always-inline-word? ] [ inline-word ] }
        { [ dup standard-generic? ] [ inline-standard-method ] }
        { [ dup math-generic? ] [ inline-math-method ] }
        { [ dup inline? ] [ inline-word ] }
        [ 2drop f ]
    } cond ;

: do-inlining ( #call word -- ? )
    [
        dup custom-inlining? [ 2dup inline-custom ] [ f ] if
        [ 2drop t ] [ (do-inlining) ] if
    ] with-scope ;
