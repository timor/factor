! Copyright (C) 2008, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs byte-arrays classes classes.algebra
classes.singleton classes.tuple classes.tuple.private combinators
combinators.short-circuit compiler.tree.propagation.copy compiler.utilities
compiler.tree.propagation.escaping
delegate kernel layouts math math.intervals namespaces sequences
graphs
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
    ;

DEFER: value-info
DEFER: value-infos
DEFER: value-info-union
DEFER: set-value-info
DEFER: set-inner-value-info

TUPLE: lazy-info { values read-only } { ro? read-only } { cached read-only } { baked? read-only } ;
: >lazy-info< ( lazy-info -- values ro? cached baked? )
    tuple-slots first4 ;

: recompute-lazy-info ( values -- info )
   [ value-info ] [ value-info-union ] map-reduce ;

: <lazy-info> ( values ro? -- obj )
    [ members dup [ record-virtual-value ] each ] dip
    over recompute-lazy-info f lazy-info boa ; inline

: lazy-ro-info? ( info -- ? )
    { [ lazy-info? ] [ ro?>> ] } 1&& ;

SYMBOL: lazy-info-trace

! TODO: Can introduce caching, would check for invalidation here
: lazy-info>info ( obj -- info )
    dup baked?>>
    [ cached>> ]
    [ values>> recompute-lazy-info ] if ;

GENERIC: >info ( info -- info )
M: value-info-state >info ;
M: f >info ;
M: lazy-info >info lazy-info>info ;

DEFER: object-info
: safe-lazy-info>info ( obj -- info )
    dup lazy-info-trace get member?
    [ drop object-info ]
    [ lazy-info-trace [ over suffix ] change
      lazy-info>info ] if ;

GENERIC: bake-info* ( info -- info )
! Check circularity

: bake-info ( info/f -- info/f )
    dup [ bake-info* ] when ;

M: value-info-state bake-info*
    clone
    [ [ bake-info ] map ] change-slots
    f >>origin
    ;

M: lazy-info bake-info*
    [
        [ values>> ]
        [ ro?>> ]
        [ safe-lazy-info>info bake-info ] tri
        t lazy-info boa
    ] with-scope ;

CONSULT: value-info-state lazy-info lazy-info>info ;

PREDICATE: live-lazy-info < lazy-info baked?>> not ;

GENERIC: thaw-info ( info -- info )
M: f thaw-info ;
M: value-info-state thaw-info
    ! Not cloning, use in init position!
    ! clone
    [ [ thaw-info ] map ] change-slots ;
M: live-lazy-info thaw-info ;
M: lazy-info thaw-info
    >lazy-info< 2drop <lazy-info> ;

: unique-definer ( lazy-info -- values ? )
    values>> members dup length 1 = ;

! Cloning is currently only well-defined during propagation of (clone)

ERROR: cannot-clone-lazy-info lazy-info ;
M: lazy-info clone cannot-clone-lazy-info ;

ERROR: cannot-set-lazy-info-slots value lazy-info ;

M: lazy-info class<< cannot-set-lazy-info-slots ;
M: lazy-info interval<< cannot-set-lazy-info-slots ;
M: lazy-info literal<< cannot-set-lazy-info-slots ;
M: lazy-info literal?<< cannot-set-lazy-info-slots ;
M: lazy-info slots<< cannot-set-lazy-info-slots ;
M: lazy-info origin<< cannot-set-lazy-info-slots ;
M: lazy-info virtual-infos<< cannot-set-lazy-info-slots ;


: <virtual-value> ( -- value )
    <value>
    [ introduce-value ]
    [ record-virtual-value ]    ! Not necessary if we have the set of virtuals
    ! accessible by local definitions only
    [  ] tri ;

: introduce-virtual-value/info ( info -- value )
    <value>
    [ introduce-value ]
    [ set-inner-value-info ]
    [ ] tri ;

! NOTE: caching on literals here to ensure that propagating over the same #push
! twice will yield the same virtual-values

! TODO: Check if we need the same for boas.  There it is not apparent at the
! info what the source is, though.

: info>values ( value-info -- seq )
    dup lazy-info?
    [ values>> ]
    [ introduce-virtual-value/info 1array ] if ;

! Things to put inside value info slot entries
DEFER: <literal-info>

! If allocating or modifying value info in branch scope, make a virtual phi
! after branch return
SYMBOL: inner-values

: record-inner-value ( value -- )
    resolve-copy
    inner-values get ?last [ adjoin ] [ drop ] if* ;

! Prevent infinite recursion while merging
! Maps literals to values
SYMBOL: slot-ref-history
SYMBOL: literal-values
! TODO: remove after debugging ( or keep as global value numbering? )
literal-values [ IH{ } clone ] initialize

: slot-ref-recursion? ( value -- ? )
    slot-ref-history get in? ;

: literal>value ( literal -- value )
    literal-values get [ drop <value> [ introduce-value ] keep ] cache ;

SYMBOL: propagate-rw-slots
: propagate-rw-slots? ( -- ? ) propagate-rw-slots get >boolean ; inline

! NOTE: discarding value, only using for recursion prevention
! Returns an info for a literal tuple slot
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

TUPLE: input-ref { index read-only } ;
: <input-ref> ( index -- obj )
    input-ref boa [ record-allocation ] keep ;

SINGLETON: limbo
CONSTANT: pointer-info T{ value-info-state { class object } { interval full-interval } { origin HS{ limbo } } }

TUPLE: literal-allocation literal ;
C: <literal-allocation> literal-allocation
: same-literal-allocation? ( allocation literal-allocation -- ? )
    2dup [ literal-allocation? ] both?
    [ [ literal>> ] bi@ eq? ]
    [ 2drop f ] if ;
SINGLETON: local-allocation

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

UNION: fixed-length array byte-array string ;
UNION: storage-class tuple fixed-length ;

! Literal tuple
: tuple-slot-infos ( tuple -- slots )
    [ tuple-slots ] [ class-of all-slots ] bi
    [ read-only>> [ <literal-info> ] [ drop f ] if ] 2map
    f prefix ;

: tuple-slot-infos-rw ( tuple -- slots )
    tuple-slots [ <literal-slot-ref> ] map f prefix ;

: immutable-tuple-literal? ( tuple -- ? )
    { [ class-of immutable-tuple-class? ]
      [ tuple-slots [
            { [ immutable-tuple-literal? ]
              [ storage-class? not ] } 1||
        ] all? ]
    } 1&& ;

: literal-class ( obj -- class )
    dup singleton-class? [
        class-of dup class? [
            drop tuple
        ] unless
    ] unless ;

: (slots-with-length) ( length-info class -- slots )
    "slots" word-prop length 1 - f <array> swap prefix ;

: (slots-with-length-rw) ( length-info class -- slots )
    [ info>values t <lazy-info> ] dip "slots" word-prop length 1 - f <array> swap prefix ;

! Literal fixed-length-sequence
: slots-with-length ( seq -- slots )
    [ length <literal-info> ] [ class-of ] bi (slots-with-length) ;

DEFER: value-infos-union
! Mis-using slots here: adding an additional one which represents the summary
! info for all element accesses
: slots-with-length-rw ( seq -- slots )
    [ [ length <literal-info> ] [ class-of ] bi
      (slots-with-length-rw) ]
    [ [ <literal-info> ] { } map-as value-infos-union info>values f <lazy-info> ] bi
    suffix ;

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
        { [ dup fixed-length? ] [
              propagate-rw-slots?
              [ slots-with-length-rw ]
              [ slots-with-length ] if
              >>slots ] }
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

DEFER: read-only-slot?

: slot-info>lazy-info ( info/f i class -- lazy-info/f )
    pick [
        [ info>values ] 2dip
        [ 1 + ] dip
        read-only-slot? <lazy-info>
    ]
    [ 3drop f ] if ;

: init-slots ( info -- info )
    propagate-rw-slots? [
        dup class>>
        '[ [ _ slot-info>lazy-info ] map-index
           [ f ] when-empty
         ] change-slots
    ] when
    ; inline

! If we have rw-info, this info has been touched and doesn't need to be
! initialized again. Alterntively, we need another flag on the value info that
! indicates modification...
: has-virtual-slots? ( info -- ? )
    slots>> [ lazy-info? ] any? ; inline

: maybe-make-literal ( info -- literal literal? )
    dup has-virtual-slots? [ [ literal>> ] [ literal?>> ] bi ]
    [ [ class>> ] [ interval>> ] bi interval>literal ] if ;

! Three cases: fresh literal, non-fresh-literal, non-literal
! non-fresh literal
: init-value-info ( info -- info )

    dup { [ literal?>> ]
          [ propagate-rw-slots? [ has-virtual-slots? not ] [ drop t ] if ]
    } 1&& [
        init-literal-info
    ] [
        dup empty-set? [
            null >>class
            empty-interval >>interval
        ] [
            init-interval
            dup maybe-make-literal
            [ >>literal ] [ >>literal? ] bi*
            [ fix-capacity-class ] change-class
        ] if
    ] if
    [ dup null? [ drop f ] when ] change-origin
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
    init-value-info
    init-slots ; foldable

! Non-literal sequence constructor
: <sequence-info> ( length class -- info )
    <value-info>
        over >>class
        [ (slots-with-length) ] dip swap >>slots
    init-value-info ;

: <rw-sequence-info> ( element length class -- info )
    <value-info>
    over >>class
    [ (slots-with-length-rw) ] dip
    rot info>values f <lazy-info> swapd suffix >>slots ;

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
    init-value-info
    init-slots ;


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

! NOTE: Union semantics! if one info has no info (f), the other info's slots are
! used.  I.e. the slots slot = f is the same as all object-info.
: intersect-slots ( info1 info2 -- slots )
    [ slots>> ] bi@ {
        { [ dup not ] [ drop ] }
        { [ over not ] [ nip ] }
        [
            f pad-tail-shorter
            [ intersect-slot ] 2map
        ]
    } cond ;

: merge-origin ( info1 info2 -- slot-refs )
    [ origin>> ] bi@ union HS{ } set-like ;

: (value-info-intersect) ( info1 info2 -- info )
    [ <value-info> ] 2dip
    {
        [ [ class>> ] bi@ class-and >>class ]
        [ [ interval>> ] bi@ interval-intersect >>interval ]
        [ intersect-literals [ >>literal ] [ >>literal? ] bi* ]
        [ intersect-slots >>slots ]
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

! NOTE: we only keep the values of non-baked union elements here.  This case
! should anyways only happen during recursive propagation.  For fixed-point
! checking, it does not matter, because the resulting union is not used.  For
! regular #phi unions, there should only be live values anyways.  The important
! case is for loop generalization, where the generalized values for next
! iteration start need to reflect the effect of the values that we now throw
! away.  However, that should actually be handled explicitly by counter
! generalization, which then only keeps the lazy-slot which was introduced into
! the loop.
: union-lazy-slot ( info1 info2 -- info )
    [ [ values>> ] bi@ union ]
    [ [ ro?>> ] bi@ and ] 2bi <lazy-info> ;


! If f, the other wins (union with null-info)
: union-slot ( info1 info2 -- info )
    {
        { [ dup not ] [ nip ] }
        { [ over not ] [ drop ] }
        { [ propagate-rw-slots? [ 2dup [ lazy-info? ] both? ] [ f ] if ] [ union-lazy-slot ] }
        [ (value-info-union) ]
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

! TODO: unused.  If this is really not needed, than it means that all inner
! value changes which have to be transported upwards have value-info-union semantics.
: refine-inner-value-info ( info value -- )
    resolve-copy dup record-inner-value
    value-infos get
    [ assoc-stack [ value-info-intersect ] when* ] 2keep
    last set-at ;

DEFER: refine-value-info

! clones
: add-info-origin ( info slot-ref -- info )
    swap clone [ HS{ } or clone [ adjoin ] keep ] change-origin ;

: register-origin ( value slot-refs -- )
    object-info clone swap >>origin
    swap refine-value-info ;

: 1register-origin ( value slot-ref -- )
    dup record-allocation
    1array >hash-set register-origin ;

! Escaping: A value that has slots has unknown slots after escaping.
! Slots contain virtual values.  Virtual values represent mutable memory
! locations.  If a virtual escapes, its info and its slots are unknown
! afterwards.
! So: If obj escapes
! - collect all reachable virtuals
! - set all virtuals to object-info, UNLESS this virtual was allocated in a
! read-only location.

GENERIC: nested-values* ( info -- lazy-infos )
M: f nested-values* drop f ;
M: value-info-state nested-values*
    slots>> ;
M: lazy-info nested-values*
    values>> [ value-info nested-values* ] gather ;

: virtuals-closure ( value -- virtuals )
    [ nested-values* ] closure members ;

: slot-virtuals-closure ( value -- virtuals )
    value-info slots>> [ virtuals-closure ] gather ;

DEFER: extend-value-info
! Full invalidation
: invalidate-object ( value -- )
    pointer-info swap extend-value-info ;

: invalidate-virtual ( value-info -- )
    dup lazy-info?
    [ dup lazy-ro-info?
      [ drop ]
      [ values>> [ invalidate-object ] each ] if
    ] [ drop ] if ;

: object-escapes ( value -- )
    slot-virtuals-closure [ invalidate-virtual ] each ;

: read-only-slot? ( n class -- ? )
    dup class?
    [ all-slots [ offset>> = ] with find nip
      dup [ read-only>> ] when ]
    [ 2drop f ] if ;

! Intersection semantics
: refine-value-info ( info value -- )
    resolve-copy value-infos get
    [ assoc-stack [ value-info-intersect ] when* ] 2keep
    last set-at ;

! Union semantics
! always records this as an inner value, because this will only make sense when
! treated with phi semantics on branch return.
! TODO: should never be a lazy info!
: extend-value-info ( info value -- )
    [ value-info-state check-instance ] dip
    dup record-inner-value
    resolve-copy value-infos get
    [ assoc-stack [ value-info-union ] when* ] 2keep
    last set-at ;

: strong-update ( info value -- )
    set-inner-value-info ;

: weak-update ( new-info virtuals -- )
    [ extend-value-info ] with each ;

: update-lazy-info ( info lazy-info -- )
    dup { [ lazy-info? ] [ ro?>> not ] } 1&&
    [ unique-definer
      [ first strong-update ]
      [ [ weak-update ] with each ] if ]
    [ 2drop ] if ;


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

: clone-virtual ( value -- value )
    value-info introduce-virtual-value/info ;


: clone-lazy-info ( lazy-info -- lazy-info )
    {
        [ values>> [ clone-virtual ] map ]
        [ ro?>> ]
        [ cached>> ]            ! TODO: re-cache?
        [ baked?>> ]
    } cleave lazy-info boa ;

! Fresh slots allocation
: cloned-value-info ( value-info -- value-info' )
    clone f >>literal f >>literal?
    [ [ dup [ dup lazy-info?
              [ clone-lazy-info ]
            [ cloned-value-info ] if
         ] when ] map ] change-slots ;
