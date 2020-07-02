! Copyright (C) 2008, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs byte-arrays classes classes.algebra classes.tuple
classes.tuple.private combinators combinators.short-circuit compiler.tree
compiler.tree.propagation.copy compiler.tree.propagation.info
compiler.tree.propagation.nodes kernel math namespaces sequences slots.private
strings words ;
IN: compiler.tree.propagation.slots

! * Optimizing Local Slot Accesses

! Rationale: For a given tree of nodes, once we encounter a set-slot call, we
! can assume the output info of any slot-call to that same tuple/array to be
! that, until another set-slot call is encountered.  In a true asynchronous
! multithreading context, we would have to "delete" that assumption if there is
! any synchronization primitive before a slot call.

PREDICATE: slot-call < #call word>> \ slot = ;
PREDICATE: set-slot-call < #call word>> \ set-slot = ;

! * Implementation Strategy
! The `slot-states` context variable holds mappings from SSA-values representing
! instances (tuples, TODO arrays) and slots to a value, to a pair representing
! the value specifier $val$ and the info of $slot$ at the time of access:
! $obj → slot → val$.  This is local to linear control flow, and
! updated every time a `set-slot` call is encountered.  Note that we include in
! $val$ the information to discern whether this is an SSA Value, or we only have
! the value-info of the slot contents (see below).

! Whenever a `slot` call is encountered, this object is queried, and if the slot
! matches (see below), the value is used to set the output info.

! Note that the reference to $slot$ and $val$ can be SSA values as long there is
! only linear code.  This allows us to treat the output value of a `slot` call as
! a copy of the input to the `set-slot` call.  This is important, since there are
! two things that we want to be able to tell:
! 1. What is the value info of the `slot` call output?
! 2. Is the `slot` call output actually a copy of something we already know?

! The first case's importance is obvious, as we want to be able to perform the
! typical type inference.  The second case is important for a different reason:
! Given e.g. tuple $T_1$ with slot $a$, and tuple $T_2$ with slot $b$, consider
! the following sequence:
! #+begin_example
! foo → T_1.a
! T_1.a -> T_2.b
! ...
! T_2.b -> X
! X.a
! #+end_example
! In this case, we want to be able to detect that the result of the last access is
! in fact the same value as $foo$.  This case is not uncommon, as a lot of
! combinators are implemented using `curried` tuples, which then contain the
! object in question.

! To summarize the strategy:
! 1. If we can prove that a slot access contains a copy of a value, use the copy
!    mechanism
! 2. If we can not prove that a slot access contains a copy of a value, but have
!    input information for the current slot state, use at least this information
!    for output type detection.

! The first case is the strongest, and type inference works as expected since any
! `value-info` call resolves the copies.  The second case could be implemented in
! two ways: (a) Using the value-info on the `slots` slot of the actual value,
! (b) looking up the info in the context on `slot` calls.

! Implementing (a) would mean carefully considering existing slot propagation as
! to how to extend the current mechanism, which is only invoked for read-only
! slots.  (b) is independent of that, since it would be implemented using the
! constraint mechanism of the `slot` call.

! In both cases, the copy information needs to be handled in a special way, since
! there is no infrastructure at the moment which can trace copies out of
! branches.  As with all other local state variables containing information, it
! must be merged at `#phi` nodes.  There are two general cases here:

! 1. Slot accesses in all branches return the same SSA value (after resolving
!    copies)
! 2. Slot access in all branches can return different SSA values.

! In the former case, we can keep the information that the slot still contains a
! copy of a unique known SSA value.  In the latter case, we have to resolve and
! merge value infos, as is done for regular phi outputs.

! ** Equivaluence of Slot Accesses

! Two slot accesses are considered to refer to the same value when
! - The $obj$ SSA-values are resolved to the same copy, and
!   1. The $slot$ SSA-values are resolved to the same copy, or
!   2. The value info of the $slot$ values are identical at the time of the slot
!      accesses.

! The first case allows us to track non-literal accesses as well as literal slot accesses.


SYMBOL: slot-states
TUPLE: slot-state slot-info value-info copy-of ;

: <slot-state> ( slot-val value-val -- obj )
    [ [ value-info ] bi@ ] keep slot-state boa ;

! Find the slot assoc of the obj assoc and record the slot state there
: update-slot-state ( value-val obj-val slot-val -- )
    [ nip swap <slot-state> ]
    [ drop slot-states get [ drop H{  } clone ] cache nip ]
    [ 2nip swap set-at ] 3tri ;

! Whether the given SLOT-VAL denotes the same slot as STATE when it was written to.
: slot-matches? ( slot-val state -- ? )
    [ value-info ] [ slot-info>> ] bi*
    { [ [ literal?>> ] both? ]
      [ [ literal>> ] bi@ = ] } 2&& ;

: lookup-slot-state ( obj-val slot-val -- value-val/f )
    swap slot-states get at
    [ ! ket-slot-val slot-val state
     { [ drop = ]
       [ nipd slot-matches? ]
     } 3||
    ] with assoc-find [ nip ] [ 2drop f ] if ;

! -- End of slot-state stuff

: sequence-constructor? ( word -- ? )
    { <array> <byte-array> (byte-array) <string> } member-eq? ;

: propagate-sequence-constructor ( #call word -- infos )
    [ in-d>> first value-info ]
    [ "default-output-classes" word-prop first ] bi*
    <sequence-info> 1array ;

: fold-<tuple-boa> ( values class -- info )
    [ [ literal>> ] map ] dip slots>tuple
    <literal-info> ;

! Return a seq with only these value infos which belong to a read-only slot.
: read-only-slots ( values class -- slots )
    all-slots
    [ read-only>> [ value-info ] [ drop f ] if ] 2map
    f prefix ;

! The first slot seems to be reserved for an array length, always.  Because of
! that, it is ignored here.  Identity-tuples are not folded in any case.
: fold-<tuple-boa>? ( values class -- ? )
    [ rest-slice [ dup [ literal?>> ] when ] all? ]
    [ identity-tuple class<= not ]
    bi* and ;

: (propagate-<tuple-boa>) ( values class -- info )
    [ read-only-slots ] keep 2dup fold-<tuple-boa>?
    [ [ rest-slice ] dip fold-<tuple-boa> ] [ <tuple-info> ] if ;

: propagate-<tuple-boa> ( #call -- infos )
    in-d>> unclip-last
    value-info literal>> first (propagate-<tuple-boa>) 1array ;

: read-only-slot? ( n class -- ? )
    all-slots [ offset>> = ] with find nip
    dup [ read-only>> ] when ;

! This one is called when the slot and the object are literal..., but only on
! read-only slots.  Note that the mechanism which records local slot accesses
! during propagation has some overlap with this.
: literal-info-slot ( slot object -- info/f )
    {
        [ class-of read-only-slot? ]
        [ nip layout-up-to-date? ]
        [ swap slot <literal-info> ]
    } 2&& ;

! This one is called when a literal slot number has been supplied to a slot call
: value-info-slot ( slot info -- info' )
    {
        { [ over 0 = ] [ 2drop fixnum <class-info> ] } ! I think this the array ! length accessor case...
        { [ dup literal?>> ] [ literal>> literal-info-slot ] }
        [ [ 1 - ] [ slots>> ] bi* ?nth ]
    } cond [ object-info ] unless* ;

: set-slot-call-propagate-after ( node -- )
    in-d>> resolve-copies first3 update-slot-state ;
