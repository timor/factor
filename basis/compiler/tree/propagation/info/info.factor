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

! If allocating or modifying value info in branch scope, make a virtual phi
! after branch return
SYMBOL: inner-values

: record-inner-value ( value -- )
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

: literal>value ( literal -- value )
    literal-values get [ drop <value> [ introduce-value ] keep ] cache ;

SYMBOL: propagate-rw-slots
: propagate-rw-slots? ( -- ? ) propagate-rw-slots get >boolean ; inline

TUPLE: ref-link { defined-by read-only } { defines read-only } ;
C: <ref-link> ref-link
: <ref-link-also-defines> ( value ref-link -- ref-link )
    [ defined-by>> ] [ defines>> ] bi
    rot suffix <ref-link> ;

: <ref-link-defined-by> ( value ref-link -- ref-link )
    [ 1array ] dip defines>> <ref-link> ;

M: f defined-by>> drop f ;
M: f defines>> drop f ;

! NOTE: discarding value, only using for recursion prevention
! Returns an info for a literal tuple slot
! TODO: handle case of nested rw-allocation in literal escaping
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
    f >>backref                 ! If something is declared literal, it can not have escaped
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

! If we have object info, and no references, then you got an eff !!1!
: init-slots ( info -- info )
    [ [ [ dup object-info = [ drop f ] when ] map ]
      [ f ] if*
      dup [ not ] all? [ drop f ] when
    ] change-slots ; inline

: init-value-info ( info -- info )
    dup literal?>> [
        init-literal-info
    ] [
        dup empty-set? [
            null >>class
            empty-interval >>interval
        ] [
            init-interval
            init-slots
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

: merge-ref-links ( info1 info2 -- ref-link )
    [ backref>> ] bi@
    [ [ defined-by>> ] bi@ union ]
    [ [ defines>> ] bi@ union ] 2bi
    2dup [ empty? ] both?
    [ 2drop f ] [ <ref-link> ] if ;

: (value-info-intersect) ( info1 info2 -- info )
    [ <value-info> ] 2dip
    {
        [ [ class>> ] bi@ class-and >>class ]
        [ [ interval>> ] bi@ interval-intersect >>interval ]
        [ intersect-literals [ >>literal ] [ >>literal? ] bi* ]
        [ intersect-slots >>slots ]
        ! Setting links is explicit, by they can be merged
        ! ! Ref-links have refinement semantics
        ! [ merge-ref-links >>backref ]
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

: union-slots ( info1 info2 -- slots )
    [ slots>> ] bi@
    object-info pad-tail-shorter
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
        [ merge-ref-links >>backref ]
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

: set-defining-value ( defining-value defined-value -- )
    [ value-info clone [ <ref-link-defined-by> ] change-backref ]
    [ set-inner-value-info ] bi ;

: add-defined-value ( defined-value defining-value -- )
    [ value-info clone [ <ref-link-also-defines> ] change-backref ]
    [ set-inner-value-info ] bi ;

: add-value-definition ( defining-value defined-value -- )
    [ set-defining-value ]
    [ swap add-defined-value ] 2bi ;

: read-only-slot? ( n class -- ? )
    dup class?
    [ all-slots [ offset>> = ] with find nip
      dup [ read-only>> ] when ]
    [ 2drop f ] if ;

: invalidate-slot ( info n class -- info )
    read-only-slot?
    [ backref>> object-info clone swap >>backref ] unless ;

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
