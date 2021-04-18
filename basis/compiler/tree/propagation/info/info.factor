! Copyright (C) 2008, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs byte-arrays classes classes.algebra
classes.singleton classes.tuple classes.tuple.private combinators
combinators.short-circuit compiler.tree.propagation.copy compiler.utilities
delegate kernel layouts math math.intervals namespaces sequences
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
    backref
    ;

! Things to put inside value info slot entries
DEFER: value-info
DEFER: value-infos
DEFER: value-info-union
DEFER: <literal-info>
DEFER: object-info
TUPLE: slot-ref { definers read-only } info ;

! TODO: may be unnecessary
! Prevent infinite recursion while merging
SYMBOL: slot-value-history

! If allocating or modifying value info in branch scope, make a virtual phi
! after branch return
SYMBOL: inner-slot-ref-values
: record-slot-ref-value ( value -- )
    inner-slot-ref-values get [ adjoin ] [ drop ] if* ;

: safe-value-infos-union ( values -- info )
    [ [ dup slot-value-history get in?
        [ drop object-info ]
        [ [ slot-value-history [ swap suffix ] change ]
          [ value-info ] bi ] if ]
      [ value-info-union ] map-reduce
    ] with-scope ;

! NOTE: dereferencing is done eagerly now.  Could switch to context-sensitivity,
! for debugging a comparison to live environment...
: <slot-ref> ( values -- obj )
    dup safe-value-infos-union slot-ref boa ;
    ! [ value-info ] [ value-info-union ] map-reduce slot-ref boa ;

: <1slot-ref> ( value -- obj ) 1array <slot-ref> ; inline
CONSULT: value-info-state slot-ref info>> ;
: set-global-value-info ( info value -- )
    resolve-copy value-infos get first set-at ;
: <literal-slot-ref> ( literal -- slot-ref )
    <literal-info>
    <value>
    {
        [ introduce-value ]
        [ set-global-value-info ]
        [ record-slot-ref-value ]
        [ 1array <slot-ref> ]
    } cleave
    ;

SINGLETON: unknown-slot
CONSULT: value-info-state unknown-slot drop object-info ;

CONSTANT: null-info T{ value-info-state f null empty-interval }

CONSTANT: object-info T{ value-info-state f object full-interval }

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
    [ read-only>> [ <literal-slot-ref> ] [ drop f ] if ] 2map
    f prefix ;

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
        { [ dup tuple? ] [ tuple-slot-infos >>slots ] }
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

: init-value-info ( info -- info )
    dup literal?>> [
        init-literal-info
    ] [
        dup empty-set? [
            null >>class
            empty-interval >>interval
        ] [
            init-interval
            dup [ class>> ] [ interval>> ] bi interval>literal
            [ >>literal ] [ >>literal? ] bi*
            [ fix-capacity-class ] change-class
        ] if
    ] if ; inline

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

! Non-literal tuple info, slot refs instead
: <tuple-ref-info> ( slot-values class -- info )
    <value-info>
    swap >>class
    swap [ dup [ resolve-copy [ record-slot-ref-value ] [ <1slot-ref> ] bi ] when ] map >>slots
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

DEFER: value-info-intersect

DEFER: (value-info-intersect)

: intersect-slot ( info1 info2 -- info )
    {
        { [ dup not ] [ nip ] }
        { [ over not ] [ drop ] }
        [ (value-info-intersect) ]
    } cond ;

: intersect-slots ( info1 info2 -- slots )
    [ slots>> ] bi@ {
        { [ dup not ] [ drop ] }
        { [ over not ] [ nip ] }
        [
            2dup [ length ] same?
            [ [ intersect-slot ] 2map ] [ 2drop f ] if
        ]
    } cond ;

: (value-info-intersect) ( info1 info2 -- info )
    [ <value-info> ] 2dip
    {
        [ [ class>> ] bi@ class-and >>class ]
        [ [ interval>> ] bi@ interval-intersect >>interval ]
        [ intersect-literals [ >>literal ] [ >>literal? ] bi* ]
        [ intersect-slots >>slots ]
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

: union-slot ( info1 info2 -- info )
    {
        { [ dup not ] [ nip ] }
        { [ over not ] [ drop ] }
        [ (value-info-union) ]
    } cond ;

: slot-ref>info ( ref/info/f -- info/f )
    dup slot-ref? [ info>> ] when ;

! TODO: Ensure it is valid with regards to escape invalidation to drop reference
! property here.
: union-slot-ref ( ref/info1 ref/info2 -- info )
    2dup [ slot-ref? ] both?
    [ [ definers>> ] bi@ union <slot-ref> ]
    [ [ slot-ref>info ] bi@ union-slot ] if ;

: union-slots ( info1 info2 -- slots )
    [ slots>> ] bi@
    object-info pad-tail-shorter
    [ union-slot-ref ] 2map ;

SYMBOL: orphan
orphan [ <value> ] initialize

: (value-info-union) ( info1 info2 -- info )
    [ <value-info> ] 2dip
    {
        [ [ class>> ] bi@ class-or >>class ]
        [ [ interval>> ] bi@ interval-union >>interval ]
        [ union-literals [ >>literal ] [ >>literal? ] bi* ]
        [ union-slots >>slots ]
        [ [ backref>> ] bi@ union >>backref ]
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

: refine-value-info ( info value -- )
    resolve-copy value-infos get
    [ assoc-stack [ value-info-intersect ] when* ] 2keep
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
