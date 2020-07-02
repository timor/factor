! Copyright (C) 2008, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs byte-arrays classes
classes.algebra classes.tuple classes.tuple.private combinators
combinators.short-circuit compiler.tree.propagation.info kernel
math sequences slots.private strings words ;
IN: compiler.tree.propagation.slots

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
