! Copyright (C) 2008, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs byte-arrays classes classes.algebra
classes.singleton classes.tuple classes.tuple.private combinators
combinators.short-circuit compiler.tree.propagation.copy compiler.utilities
compiler.tree.propagation.escaping
delegate kernel layouts math math.intervals namespaces sequences
hash-sets
sequences.private sets stack-checker.values strings words ;
IN: compiler.tree.propagation.info

: false-class? ( class -- ? ) \ f class<= ;

: true-class? ( class -- ? ) \ f class-not class<= ;

: null-class? ( class -- ? ) null class<= ;

GENERIC: eql? ( obj1 obj2 -- ? )
M: object eql? eq? ;
M: fixnum eql? eq? ;
M: bignum eql? over bignum? [ = ] [ 2drop f ] if ;
M: ratio eql? over ratio? [ = ] [ 2drop f ] if ;
M: float eql? over float? [ [ double>bits ] same? ] [ 2drop f ] if ;
M: complex eql? over complex? [ = ] [ 2drop f ] if ;

TUPLE: value-info-state
    class
    interval
    literal
    literal?
    slots
    origin
    slot-refs
    ;

DEFER: value-info
DEFER: value-infos
DEFER: value-info-union
DEFER: set-value-info
DEFER: set-inner-value-info

TUPLE: lazy-info values ;
C: <lazy-info> lazy-info
: lazy-info>info ( obj -- info )
    values>> [ value-info ] [ value-info-union ] map-reduce ;
GENERIC: bake-info* ( info -- info )
! TODO: check circularity
: bake-info ( info/f -- info/f )
    dup [ bake-info* ] when ;
M: value-info-state bake-info*
    clone f >>slot-refs f >>origin
    [ [ bake-info ] map ] change-slots ;
M: lazy-info bake-info*
    lazy-info>info bake-info ;

CONSULT: value-info-state lazy-info lazy-info>info ;
: info>values ( value-info -- values )
    dup lazy-info?
    [ values>> ]
    [ <value>
      [ introduce-value ]
      [ set-inner-value-info ]
      [ 1array ] tri ] if ;

! Things to put inside value info slot entries
DEFER: <literal-info>
DEFER: object-info

! If allocating or modifying value info in branch scope, make a virtual phi
! after branch return
SYMBOL: inner-values

: record-inner-value ( value -- )
    resolve-copy
    inner-values get [ adjoin ] [ drop ] if* ;

! Prevent infinite recursion while merging
! Maps literals to values
SYMBOL: slot-ref-history
SYMBOL: literal-values
! TODO: remove after debugging ( or keep as global value numbering? )
literal-values [ IH{ } clone ] initialize

: slot-ref-recursion? ( value -- ? )
    slot-ref-history get in? ;

: set-global-value-info ( info value -- )
    resolve-copy value-infos get first set-at ;

! TODO: use in deliteralization
: literal>value ( literal -- value )
    literal-values get [ drop <value> [ introduce-value ] keep ] cache ;

SYMBOL: propagate-rw-slots
: propagate-rw-slots? ( -- ? ) propagate-rw-slots get >boolean ; inline


! NOTE: discarding value, only using for recursion prevention
! Returns an info for a literal tuple slot
! TODO: handle case of nested rw-allocation in literal escaping
! TODO: wrong name in new slot-ref context
: <literal-slot-ref> ( literal -- info )
    dup literal>value
    dup slot-ref-recursion?
    [ 2drop object-info ]
    [
        [
            slot-ref-history [ swap suffix ] change
            <literal-info>
        ] with-scope
    ] if ;

CONSTANT: null-info T{ value-info-state f null empty-interval }

CONSTANT: object-info T{ value-info-state f object full-interval }

! Slot reference protocol
! Get current value of referenced info

! FIXME: better name would be "updatable..."
GENERIC: mutable? ( slot-ref -- ? )
GENERIC: dereference ( slot-ref -- slot-info )
GENERIC: weak-update ( new-info slot-ref -- )
GENERIC: strong-update ( new-info slot-ref -- )
GENERIC: container-info ( slot-ref -- info )
! GENERIC: nofity-slot-change ( slot-ref -- )
M: object mutable? drop f ;
M: object weak-update 2drop ;
M: object strong-update 2drop ;
M: object dereference drop null-info ;


! This is a link to the container which contains this info
TUPLE: tuple-slot-ref { object-value read-only } { slot-num read-only } ;
C: <tuple-slot-ref> tuple-slot-ref
M: tuple-slot-ref dereference
    [ slot-num>> 1 - ] [ object-value>> value-info slots>> ] bi ?nth
    object-info or ;

! TODO: handle ro here
M: tuple-slot-ref mutable? drop t ;
M: tuple-slot-ref container-info object-value>> value-info ;

TUPLE: ro-tuple-slot-ref < tuple-slot-ref ;
! NOTE: this is mutable because there can be reference updates!
! Regular code will never attempt to modify a read-only slot
M: ro-tuple-slot-ref mutable? drop t ;
M: ro-tuple-slot-ref weak-update 2drop ;

TUPLE: input-ref { index read-only } ;
: <input-ref> ( index -- obj )
    input-ref boa [ record-allocation ] keep ;
M: input-ref container-info drop null-info ;

SINGLETON: limbo
M: limbo container-info drop null-info ;

TUPLE: literal-allocation literal ;
C: <literal-allocation> literal-allocation

TUPLE: local-allocation value ;
C: <local-allocation> local-allocation

! Literalization

: interval>literal ( class interval -- literal literal? )
    dup special-interval? [
        2drop f f
    ] [
        dup from>> first {
            { [ over interval-length 0 > ] [ 3drop f f ] }
            { [ pick bignum class<= ] [ 2nip >bignum t ] }
            { [ pick integer class<= ] [ 2nip >fixnum t ] }
            { [ pick float class<= ] [ 2nip [ f f ] [ >float t ] if-zero ] }
            [ 3drop f f ]
        } cond
    ] if ;

: <value-info> ( -- info ) \ value-info-state new ; inline

DEFER: <literal-info>

! Literal tuple
: tuple-slot-infos ( tuple -- slots )
    [ tuple-slots ] [ class-of all-slots ] bi
    [ read-only>> [ <literal-slot-ref> ] [ drop object-info ] if ] 2map
    f prefix ;

: tuple-slot-infos-rw ( tuple -- slots )
    tuple-slots [ <literal-slot-ref> ] map f prefix ;

UNION: fixed-length array byte-array string ;

: literal-class ( obj -- class )
    dup singleton-class? [
        class-of dup class? [
            drop tuple
        ] unless
    ] unless ;

: (slots-with-length) ( length class -- slots )
    "slots" word-prop length 1 - f <array> swap prefix ;

! Literal fixed-length-sequence
: slots-with-length ( seq -- slots )
    [ length <literal-info> ] [ class-of ] bi (slots-with-length) ;

: init-literal-info ( info -- info )
    empty-interval >>interval
    dup literal>> literal-class >>class
    dup literal>> {
        { [ dup real? ] [ [a,a] >>interval ] }
        { [ dup tuple? ] [
              propagate-rw-slots?
              [ tuple-slot-infos-rw ]
              [ tuple-slot-infos ] if
              >>slots ] }
        { [ dup fixed-length? ] [ slots-with-length >>slots ] }
        [ drop ]
    } cond ; inline

: empty-set? ( info -- ? )
    {
        [ class>> null-class? ]
        [ [ interval>> empty-interval? ] [ class>> real class<= ] bi and ]
    } 1|| ;

! Hardcoding classes is kind of a hack.
: min-value ( class -- n )
    {
        { fixnum [ most-negative-fixnum ] }
        { array-capacity [ 0 ] }
        { integer-array-capacity [ 0 ] }
        [ drop -1/0. ]
    } case ;

: max-value ( class -- n )
    {
        { fixnum [ most-positive-fixnum ] }
        { array-capacity [ max-array-capacity ] }
        { integer-array-capacity [ max-array-capacity ] }
        [ drop 1/0. ]
    } case ;

: class-interval ( class -- i )
    {
        { fixnum [ fixnum-interval ] }
        { array-capacity [ array-capacity-interval ] }
        { integer-array-capacity [ array-capacity-interval ] }
        [ drop full-interval ]
    } case ;

: fix-capacity-class ( class -- class' )
    {
        { array-capacity fixnum }
        { integer-array-capacity integer }
    } ?at drop ;

: wrap-interval ( interval class -- interval' )
    class-interval 2dup interval-subset? [ drop ] [ nip ] if ;

: init-interval ( info -- info )
    dup [ interval>> full-interval or ] [ class>> ] bi wrap-interval >>interval
    dup class>> integer class<= [ [ integral-closure ] change-interval ] when ; inline

: init-slots ( info -- info )
    propagate-rw-slots?
    [ [ [ dup [ info>values <lazy-info> ] when ] map ] change-slots ] when
    ; inline

    ! [ [ [ dup object-info = [ drop f ] when ] map ]
    !   [ f ] if*
    !   dup [ not ] all? [ drop f ] when
    ! ] change-slots ; inline

! TODO: maybe slot references if something was inferred literal?
: init-value-info ( info -- info )
    dup literal?>> [
        init-literal-info
    ] [
        dup empty-set? [
            null >>class
            empty-interval >>interval
        ] [
            init-interval
            ! init-slots
            dup [ class>> ] [ interval>> ] bi interval>literal
            [ >>literal ] [ >>literal? ] bi*
            [ fix-capacity-class ] change-class
        ] if
    ] if
    init-slots
    [ dup null? [ drop f ] when ] change-slot-refs
    ; inline

: <class/interval-info> ( class interval -- info )
    <value-info>
        swap >>interval
        swap >>class
    init-value-info ; foldable

: <class-info> ( class -- info )
    f <class/interval-info> ; foldable

: <interval-info> ( interval -- info )
    <value-info>
        real >>class
        swap >>interval
    init-value-info ; foldable

: <literal-info> ( literal -- info )
    <value-info>
        swap >>literal
        t >>literal?
    init-value-info ; foldable

: <sequence-info> ( length class -- info )
    <value-info>
        over >>class
        [ (slots-with-length) ] dip swap >>slots
    init-value-info ;

! Non-literal tuple info, constructor
: <tuple-info> ( slots class -- info )
    <value-info>
        swap >>class
        swap >>slots
    init-value-info ;


! Taking value-info, but assigning virtuals to the info slots
! TODO: restore to old code path
: <tuple-ref-info> ( slot-values class -- info )
    <value-info>
    swap >>class
    swap [ dup [ resolve-copy [ record-inner-value ] [ value-info ] bi ] when ] map >>slots
    init-value-info ;


: >literal< ( info -- literal literal? )
    [ literal>> ] [ literal?>> ] bi ;

: intersect-literals ( info1 info2 -- literal literal? )
    {
        { [ dup literal?>> not ] [ drop >literal< ] }
        { [ over literal?>> not ] [ nip >literal< ] }
        { [ 2dup [ literal>> ] bi@ eql? not ] [ 2drop f f ] }
        [ drop >literal< ]
    } cond ;

DEFER: (value-info-intersect)

! ! Is this actually called???
! : intersect-lazy-slot ( info1 info2 -- info )
!     [ info>values ] bi@ intersect

! NOTE: destroys lazy info if two different ones meet
: intersect-slot ( info1 info2 -- info )
    {
        { [ dup not ] [ nip ] }
        { [ over not ] [ drop ] }
        [ (value-info-intersect) ]
    } cond ;

! If f, then f
: intersect-slots ( info1 info2 -- slots )
    [ slots>> ] bi@ {
        { [ dup not ] [ drop ] }
        { [ over not ] [ nip ] }
        [
            f pad-tail-shorter
            [ intersect-slot ] 2map
        ]
    } cond ;


: merge-slot-refs ( info1 info2 -- slot-refs )
    [ slot-refs>> ] bi@ union HS{ } set-like ;

: merge-origin ( info1 info2 -- slot-refs )
    [ origin>> ] bi@ union HS{ } set-like ;

: (value-info-intersect) ( info1 info2 -- info )
    [ <value-info> ] 2dip
    {
        [ [ class>> ] bi@ class-and >>class ]
        [ [ interval>> ] bi@ interval-intersect >>interval ]
        [ intersect-literals [ >>literal ] [ >>literal? ] bi* ]
        [ intersect-slots >>slots ]
        [ merge-slot-refs >>slot-refs ]
        [ merge-origin >>origin ]
    } 2cleave
    init-value-info ;

: value-info-intersect ( info1 info2 -- info )
    {
        { [ dup class>> null-class? ] [ nip ] }
        { [ over class>> null-class? ] [ drop ] }
        [ (value-info-intersect) ]
    } cond ;

: union-literals ( info1 info2 -- literal literal? )
    2dup [ literal?>> ] both? [
        [ literal>> ] bi@ 2dup eql? [ drop t ] [ 2drop f f ] if
    ] [ 2drop f f ] if ;

DEFER: value-info-union

DEFER: (value-info-union)

: union-lazy-slot ( info1 info2 -- info )
    [ info>values ] bi@ union <lazy-info> ;

! If f, the other wins (union with null-info)
: union-slot ( info1 info2 -- info )
    {
        { [ dup not ] [ nip ] }
        { [ over not ] [ drop ] }
        [ propagate-rw-slots? [ union-lazy-slot ] [ (value-info-union) ] if ]
    } cond ;

: union-slots ( info1 info2 -- slots )
    [ slots>> ] bi@
    f pad-tail-shorter
    [ union-slot ] 2map ;

SYMBOL: orphan
orphan [ <value> ] initialize

: (value-info-union) ( info1 info2 -- info )
    [ <value-info> ] 2dip
    {
        [ [ class>> ] bi@ class-or >>class ]
        [ [ interval>> ] bi@ interval-union >>interval ]
        [ union-literals [ >>literal ] [ >>literal? ] bi* ]
        [ union-slots >>slots ]
        [ merge-slot-refs >>slot-refs ]
        [ merge-origin >>origin ]
    } 2cleave
    init-value-info ;

: value-info-union ( info1 info2 -- info )
    {
        { [ dup class>> null-class? ] [ drop ] }
        { [ over class>> null-class? ] [ nip ] }
        [ (value-info-union) ]
    } cond ;

: value-infos-union ( infos -- info )
    [ null-info ]
    [ [ ] [ value-info-union ] map-reduce ] if-empty ;

: literals<= ( info1 info2 -- ? )
    {
        { [ dup literal?>> not ] [ 2drop t ] }
        { [ over literal?>> not ] [ drop class>> null-class? ] }
        [ [ literal>> ] bi@ eql? ]
    } cond ;

DEFER: value-info<=

: slots<= ( info1 info2 -- ? )
    2dup [ class>> ] bi@ class< [ 2drop t ] [
        [ slots>> ] bi@ f pad-tail-shorter [ value-info<= ] 2all?
    ] if ;

: value-info<= ( info1 info2 -- ? )
    [ [ object-info ] unless* ] bi@
    {
        [ [ class>> ] bi@ class<= ]
        [ [ interval>> ] bi@ interval-subset? ]
        [ literals<= ]
        [ slots<= ]
    } 2&& ;

SYMBOL: value-infos

: value-info* ( value -- info ? )
    resolve-copy value-infos get assoc-stack
    [ null-info or ] [ >boolean ] bi ; inline

: value-info ( value -- info )
    value-info* drop ;

: set-value-info ( info value -- )
    resolve-copy value-infos get last set-at ;

! Scope-wise, typically `defined` is a new inner value, while
! `defined-by` is a changed outer value.

: set-inner-value-info ( info value -- )
    [ set-value-info ]
    [ record-inner-value ] bi ;

: refine-inner-value-info ( info value -- )
    resolve-copy dup record-inner-value
    value-infos get
    [ assoc-stack [ value-info-intersect ] when* ] 2keep
    last set-at ;

: ensure-slots-with ( slot-num seq/f padding -- slot-num seq )
    [ clone over ] dip pad-tail ; inline

: ensure-slots ( slot-num seq/f -- slot-num seq )
    f ensure-slots-with ; inline
    ! clone over f pad-tail ; inline

! Change info, but keep slot-ref info
! Weak update
: <updated-slot-info> ( new-info slot-info/f -- slot-info )
    object-info or [ value-info-union ] keep slot-refs>> >>slot-refs ;

! Strong update
: <override-slot-info> ( new-info slot-info/f -- slot-info )
    [ clone ] dip
    object-info or slot-refs>> >>slot-refs ;

! Weak update
:: update-slot-infos ( new-info object-value slot-num -- )
    object-value value-info :> obj-info
    obj-info clone [ slot-num swap ensure-slots
                     [ 1 - ] dip
                     [
                         ! [ new-info swap <updated-slot-info> ]
                         [ new-info value-info-union ]
                         change-nth ] keep
    ] change-slots
    object-value set-inner-value-info ;

M: tuple-slot-ref weak-update
    [ object-value>> ] [ slot-num>> ] bi update-slot-infos ;

! Strong update
:: override-slot-infos ( new-info object-value slot-num -- )
    object-value value-info :> obj-info
    obj-info clone [ slot-num swap ensure-slots
                     [ 1 - ] dip
                     [
                         ! [ new-info swap <override-slot-info> ]
                         [ drop new-info ]
                         change-nth ] keep
    ] change-slots
    object-value set-inner-value-info ;

M: tuple-slot-ref strong-update
    [ object-value>> ] [ slot-num>> ] bi override-slot-infos ;

! Use with intersection semantics
: <slot-ref-info> ( slot-ref -- info )
    object-info clone swap 1array >hash-set
    >>slot-refs ;


! Not using
! Must be applied with union semantics
: <slot-info-for-class> ( class slot-info slot-num -- tuple-info )
    [ <class-info> empty-interval >>interval ] 2dip
    f ensure-slots [ 1 - ] dip [ set-nth ] keep
    >>slots
    ;

DEFER: refine-value-info

DEFER: read-only-slot?
: make-tuple-slot-ref ( object-value slot-num -- slot-ref )
    2dup swap value-info class>> read-only-slot?
    [ ro-tuple-slot-ref boa ]
    [ <tuple-slot-ref> ] if
    dup record-allocation
    ; inline


DEFER: extend-value-info
! Register value in slot, return updated info with added slot ref
! 1. Create new slot ref (create)
! 2. Attach that to the defining value (extend)
! TODO: below is an extra step, which actually happens before
! 3. Set tuple slot to updated defining value (override)
! This then reflects the state of the object and its new slot.
! Propagation of changes is done in caller context.  This is done by propagating
! the changed CONTAINER value info back through it's slot refs, deciding whether a
! strong or weak update is possible at the corresponding allocation.

: register-slot-storage ( stored-value slot-ref -- )
    <slot-ref-info> swap refine-value-info ;

: register-tuple-slot-storage ( stored-value containing-object slot-num -- )
    make-tuple-slot-ref register-slot-storage ;

: register-origin ( value slot-refs -- )
    object-info clone swap >>origin
    swap refine-value-info ;

: 1register-origin ( value slot-ref -- )
    dup record-allocation
    1array >hash-set register-origin ;

: register-escape ( value -- )
    object-info clone HS{ limbo } >>origin
    swap extend-value-info ;

! :: set-tuple-slot-ref ( defining-value defined-object slot-num -- )
!     defined-object resolve-copy :> obj-val
!     obj-val slot-num make-tuple-slot-ref :> new-ref
!     new-ref <slot-ref-info> defining-value refine-inner-value-info
!     defined-object value-info
!     ! FIXME: this would be an application for non-mutable sequences
!     clone dup slots>> slot-num swap ensure-slots [ 1 - ] dip
!     defining-value value-info swap pick set-nth >>slots
!     defined-object set-inner-value-info ;

    ! defining-object resolve-copy :> obj-val
    ! obj-val slot-num make-tuple-slot-ref :> new-ref
    ! obj-val value-info class>>
    ! new-ref <slot-ref-info> slot-num <slot-info-for-class> obj-val extend-value-info
    ! ;
    ! defined-value value-info :> val-info
    ! val-info [ HS{ } or clone ] change-slot-refs
    !  new-ref over slot-refs>> adjoin
    ! [ defined-value set-inner-value-info ] keep ;


: read-only-slot? ( n class -- ? )
    dup class?
    [ all-slots [ offset>> = ] with find nip
      dup [ read-only>> ] when ]
    [ 2drop f ] if ;

! TODO: This destroys reference info.  Ensure that that is not a problem if this
! is actually used...
: invalidate-slot ( info n class -- info )
    read-only-slot?
    [ drop object-info ] unless ;

! Non-recursive
! TODO Maybe test here for slots before doing that, or only do it if it is an allocation?
: <invalidated-slots-info> ( info -- info )
    clone dup class>> '[
        [ 1 + over
          [ _ invalidate-slot ]
          [ 2drop f ] if
        ] map-index
    ] change-slots
    f >>literal?
    f >>interval
    init-value-info
    ;

: invalidate-slots-info ( value -- )
    [ value-info <invalidated-slots-info> ]
    [ set-inner-value-info ] bi ;

! Intersection semantics
: refine-value-info ( info value -- )
    resolve-copy value-infos get
    [ assoc-stack [ value-info-intersect ] when* ] 2keep
    last set-at ;

! Union semantics
! always records this as an inner value, because this will only make sense when
! treated with phi semantics on branch return.
: extend-value-info ( info value -- )
    dup record-inner-value
    resolve-copy value-infos get
    [ assoc-stack [ value-info-union ] when* ] 2keep
    last set-at ;

: value-literal ( value -- obj ? )
    value-info >literal< ;

: possible-boolean-values ( info -- values )
    class>> {
        { [ dup null-class? ] [ { } ] }
        { [ dup true-class? ] [ { t } ] }
        { [ dup false-class? ] [ { f } ] }
        [ { t f } ]
    } cond nip ;

: node-value-info ( node value -- info )
    swap info>> at* [ drop null-info ] unless ;

: node-input-infos ( node -- seq )
    dup in-d>> [ node-value-info ] with map ;

: node-output-infos ( node -- seq )
    dup out-d>> [ node-value-info ] with map ;

: first-literal ( #call -- obj )
    dup in-d>> first node-value-info literal>> ;

: last-literal ( #call -- obj )
    dup out-d>> last node-value-info literal>> ;

: immutable-tuple-boa? ( #call -- ? )
    dup word>> \ <tuple-boa> eq? [
        dup in-d>> last node-value-info
        literal>> first immutable-tuple-class?
    ] [ drop f ] if ;

: class-infos ( classes/f -- infos )
    [ <class-info> ] map ;

: word>input-infos ( word -- input-infos/f )
    "input-classes" word-prop class-infos ;
