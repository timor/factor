! Copyright (C) 2008, 2009 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs classes.algebra combinators
combinators.short-circuit compiler.messages compiler.tree compiler.tree.builder
compiler.tree.normalization compiler.tree.propagation.info
compiler.tree.propagation.nodes compiler.tree.recursive generic generic.math
generic.single generic.standard kernel locals math math.partial-dispatch
namespaces quotations sequences words ;
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

! This one specifies the class, method and body slots of a #call if it is
! inlined.  It works irrespective of whether the method and body slot have been
! set already.
! - If a quotation is provided:
!   - set the class slot to the provided class (which is always number for math methods???)
!   - If the method slot of the #call is equal to the provided word
!     - Assume that body is set, propagate that
!     - Otherwise compute the nodes based on the #call and the provided
!       word/quot, update the method and body slot, and propagate the body.
!       If no nodes have been provided, undo the inlining.
!
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
    2dup
    dupd inlining-standard-method eliminate-dispatch
    [ [ swap method>> "Standard Method inlined: %u -> %u" format-to-trace-file ] [ 2drop ] if ] keep
    ;

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
