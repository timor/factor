! Copyright (C) 2008, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays byte-arrays classes classes.algebra classes.tuple
classes.tuple.private combinators combinators.short-circuit
compiler.tree.propagation.info compiler.tree.propagation.reflinks kernel math
sequences slots.private strings words ;
IN: compiler.tree.propagation.slots

: sequence-constructor? ( word -- ? )
    { <array> <byte-array> (byte-array) <string> } member-eq? ;

: propagate-sequence-constructor ( #call word -- infos )
    [ in-d>> first value-info ]
    [ "default-output-classes" word-prop first ] bi*
    <sequence-info> 1array ;

: fold-<tuple-boa> ( infos class -- info )
    [ [ literal>> ] map ] dip slots>tuple
    <literal-info> ;

: read-only-slots ( values class -- slot-infos )
    all-slots
    [ read-only>> [ value-info ] [ drop f ] if ] 2map
    f prefix ;

: read-only-slots-values ( values class -- values )
    all-slots
    [ read-only>> [ drop f ] unless ] 2map
    f prefix ;

: fold-<tuple-boa>? ( infos class -- ? )
    [ rest-slice [ dup [ literal?>> ] when ] all? ]
    [ identity-tuple class<= not ]
    bi* and ;

: fold-<tuple-boa>-values? ( values class -- ? )
    [ rest-slice [ dup [ value-info literal?>> ] when ] all? ]
    [ identity-tuple class<= not ]
    bi* and ;

: (propagate-<tuple-boa>) ( values class -- info )
    [ read-only-slots ] keep 2dup fold-<tuple-boa>?
    [ [ rest-slice ] dip fold-<tuple-boa> ] [ <tuple-info> ] if ;

! Check folding like regular.  Otherwise, optionally not kill rw slots.
: fold-<tuple-boa>-rw? ( values class -- values' class ? )
    2dup [ read-only-slots-values ] keep 2dup fold-<tuple-boa>-values?
    [ 2nipd t ]
    [
        propagate-rw-slots?
        [ 2drop [ f prefix ] dip ]
        [ 2nipd ] if
        f
    ] if ;

: (propagate-<tuple-boa>-refs) ( values class -- info )
    fold-<tuple-boa>-rw?
    [ [ rest-slice [ value-info ] map ] dip fold-<tuple-boa> ] [ <tuple-ref-info> ] if ;

! Non-literal construction
: propagate-<tuple-boa>-refs ( #call -- infos )
    in-d>> unclip-last
    value-info literal>> first (propagate-<tuple-boa>-refs) 1array ; inline

: propagate-<tuple-boa> ( #call -- infos )
    propagate-<tuple-boa>-refs ;

! : propagate-<tuple-boa> ( #call -- infos )
!     in-d>> unclip-last
!     value-info literal>> first (propagate-<tuple-boa>) 1array ;

! TODO: propagate literal slots also on infos, not on literal!
! Slot call to literal object.  Will only resolve read-only slots.  Will also
! refuse to get slot info if the definition has changed in the meantime
: literal-info-slot ( slot object -- info/f )
    {
        [ class-of read-only-slot? ]
        [ nip layout-up-to-date? ]
        [ swap slot <literal-info> ]
    } 2&& ;


! slot call propagation
: value-info-slot ( slot info -- info' )
    {
        { [ over 0 = ] [ 2drop fixnum <class-info> ] }
        { [ dup literal?>> ] [ literal>> literal-info-slot ] }
        [ [ 1 - ] [ slots>> ] bi* ?nth ]
    } cond [ object-info ] unless* ;

! Backref handling
: valid-rw-slot-access? ( slot info -- ? )
    [ 1 - ] dip slots>> nth value-info-escapes? not ;


! TODO verify that escaping has set this to object-info
: mask-rw-slot-access ( slot info -- info'/f )
    2dup
    { [ class>> read-only-slot? ]
      [ { [ 2drop propagate-rw-slots? ]
          [ valid-rw-slot-access? ] } 2&& ]
    } 2||
    [ [ 1 - ] [ slots>> ] bi* ?nth ]
    [ 2drop f ] if ;

! Step 1: non-literal tuples
: value-info-slot-mask-rw ( slot info -- info' )
    {
       { [ over 0 = ] [ 2drop fixnum <class-info> ] } ! This is a length slot, why no deref?
       { [ dup literal?>> propagate-rw-slots? and ] [ mask-rw-slot-access ] }
       { [ dup literal?>> ] [ literal>> literal-info-slot ] }
       [ mask-rw-slot-access ]
    } cond [ object-info ] unless* ;
