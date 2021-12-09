USING: accessors arrays assocs assocs.extras classes classes.algebra combinators
combinators.smart compiler.tree.propagation.info continuations effects
generalizations generic.math kernel kernel.private math math.intervals
namespaces quotations sequences sequences.generalizations sets stack-checker
types.bidi words ;

IN: types.protocols
! * Type normalization protocols
! Certain type operations expect types to be in a certain shape to be able to
! apply type calculations correctly

! This should provide a coherent set of type coercions.

! Examples:
! - callables need to be cast to effects (arrow types)
! - numeric type calculations are performed on intervals

! ** General classoid coercion
! Needed for things that can be used during type inference but need to be
! compared to actual values...
GENERIC: type>classoid ( type -- classoid )
M: classoid type>classoid ;

! ** Effect type normalization
! Multiple-dispatch would be nice...
GENERIC: type>effect ( type -- effect )
PREDICATE: callable-class < class callable class<= ;
PREDICATE: literal-callable < wrapper wrapped>> callable? ;

! NOTE: not calling nested inference here.  If that is intended, it has to be
! made explicit during stepping using expansion.
M: literal-callable type>effect wrapped>> infer ;

: unknown-effect ( -- effect )
    "a" { } "b" { } <variable-effect> ;

M: callable-class type>effect drop
        unknown-effect ;

: error-effect ( -- effect )
    { } dup t <terminated-effect> ;

M: class type>effect drop error-effect ;

ERROR: unconcretized-effect-coercion ;

M: ?? type>effect unconcretized-effect-coercion ;

! * Other approach: modular value info
! quots are a hashtable of orthogonal lattices that are traversed in parallel,
! each entry having two elements, a forward and a backwards quot.
! Known lattice keys:
! literal
! class
! interval
! slot-access?

! Protocol:
! For each type key we need: bottom and top value,
! Conversion from class
! Conversion from value
! Meet and join operations?
! (Least) upper bound: join
! (Greatest) lower bound: meet

! Type keys must be independent.  Information of different states may only
! combined to decide on what code to generate next.  This is some form of
! independence guarantee so it does not matter whether we compute the compound
! of a word or its constituents.

MIXIN: type-key
TUPLE: literal-value value ;
! TUPLE: class-value class ;
! TUPLE: interval-value interval ;
TUPLE: relation value ;
TUPLE: eql-to < relation ;
TUPLE: less-than < relation ;
TUPLE: greater-than < relation ;
SINGLETON: value-id
! INSTANCE: \ literal-value type-key
INSTANCE: \ class type-key
INSTANCE: \ interval type-key
INSTANCE: \ relation type-key
INSTANCE: \ value-id type-key

! Hacky...
: all-type-keys ( -- classes )
    type-key class-members [ wrapped>> ] map ;

! NOTE: transfers are also not assumed to be undoable right now... As long as
! transitions can be rolled back atomically, that should not be a problem...
GENERIC: primitive-transfer ( state-in primitive type-value-class -- transfer-quot )
! NOTE: undos are not assumed to be undoable right now...
GENERIC: primitive-undo ( state-in primitive type-value-class -- undo-quot )
GENERIC: value>type ( value type-value-class -- type-value )
M: type-key value>type 2drop ?? ;

! There is access to a branch-id for identification
: branch-id ( -- id )
    \ branch-id get ;

GENERIC: apply-declaration ( state-in spec type-value-class -- state-in )

! Used when undo'ing duplication, i.e. the properties an output value must have to be
! compatible with two different input positions.
! TODO: name correct?

! NOTE: we could try to enforce that the order actually matters?
TUPLE: and-prop p1 p2 ;
C: <and> and-prop
TUPLE: xor-prop props ;
C: <xor> xor-prop
! TUPLE: not-prop prop ;
! C: <not> not-prop

! Combine different outputs
! Forward merge after exclusive control-path split
GENERIC: type-value-merge ( outn> type-value-class -- >out )
M: type-key type-value-merge drop <xor> ;
! Backprop merged into exclusive control-paths
! XXX
GENERIC: type-value-undo-merge ( out_i< out< type-value-class -- <out )
M: type-key type-value-undo-merge drop <and> ;
GENERIC: type-values-intersect? ( type-value1 type-value2 type-value-class -- ? )
! Re-Combination of data-path-split
GENERIC: type-value-undo-dup ( v> <v' type-value-class -- v< )
! Backprop into common history of exclusive control-paths
! GENERIC: type-value-undo-split ( v> <out )
! GENERIC: type-value-join* ( out1> out2> type-value-class -- >out' )
! ! NOTE: intended for intersection behavior when parallel-execution joins are
! ! propagated backwards
! GENERIC: type-value-undo-join* ( out1> <out' type-value-class -- out1< )
! ! GENERIC: type-value-join* ( x1< x2< x1> type-value-class -- <x1 )
! GENERIC: type-value-meet* ( x1 x2  type-value-class -- x'> )
! ! Default is to assume regular branch-independent reverse fanout.
GENERIC: top-type-value ( type-value-class -- object )
GENERIC: bottom-type-value ( type-value-class -- object )
! This is used to check a state whether it would lead to a divergent calculation
GENERIC: type-value-diverges? ( type-value type-value-class -- ? )
! Used for inputs
GENERIC: unknown-type-value ( type-value-class -- object )
M: type-key unknown-type-value drop ?? ;

ERROR: undefined-primitive-type-transfer state-in primitive type-key ;
ERROR: undefined-primitive-type-undo state-in primitive type-key ;

UNION: primitive-data-op \ dup \ drop \ swap \ rot ;

: constantly ( value -- quot )
    literalize 1quotation ;

M: type-key primitive-transfer
    {
        { [ over primitive-data-op? ] [ drop 1quotation nip ] }
        { [ over word? not ] [ value>type constantly nip ] }
        [ undefined-primitive-type-transfer ]
    } cond ;

! : undo-dup ( state-in class -- quot: ( x x -- x ) )
!     nip [ type-value-undo-dup ] curry ;

: or-unknown ( type1 type2 quot: ( type1 type2 -- type ) -- type )
    over ??? [ swapd ] when
    pick ??? [ drop nip ] [ call( x x -- x ) ] if ;

: undo-dup ( state-in class -- quot: ( x x -- x ) )
    2drop [
        2dup = [ drop ]
        [ [ <and> ] or-unknown ] if ] ;

M: type-key primitive-undo
    { { [ over \ drop eq? ] [ nip of last constantly ] }
      { [ over \ swap eq? ] [ 3drop [ swap ] ] }
      { [ over \ dup eq? ] [ nip undo-dup ] }
      { [ over \ rot eq? ] [ 3drop [ -rot ] ] }
      { [ over word? not ] [ 3drop [ drop ] ] }
      [ undefined-primitive-type-undo ]
    } cond ;

ERROR: not-a-primitive-transfer word ;

: pad-state ( state-in n key -- state-in )
    [ over length - ] dip
    over 0 >
    [ [ unknown-type-value ] curry replicate prepend ]
    [ 2drop ] if ;

:: ensure-state-in ( state-in word -- state-in )
    word in-types length :> n
    state-in [| key state |
        state n
        key pad-state
        key swap
    ] assoc-map ;

ERROR: invalid-declaration spec ;
:: ensure-declaration-in ( state-in -- state-in )
    state-in class of ?last :> spec
    spec wrapper? [ spec invalid-declaration ] unless
    spec wrapped>> :> spec
    spec length :> n
    state-in [| key state |
        state unclip-last-slice :> ( value-state decl )
        value-state n key pad-state
        spec key apply-declaration
        decl suffix key swap
     ] assoc-map  ;

! Interface function
! Used to ensure that undo and transfer functions have correct setup
: empty-state ( -- state-in )
    all-type-keys [ { } ] H{ } map>assoc ;

: ensure-inputs ( state-in word -- state-in word )
    [ [ empty-state ] unless* ] dip
    dup \ declare eq?
    [ [ ensure-declaration-in ] dip ]
    [ [ ensure-state-in ] keep ] if ;

: compute-key-undo ( state-in word key -- undo-quot )
    primitive-undo ;

: compute-key-transfer ( state-in word key -- quot )
    primitive-transfer ;

! Return two assocs, one for the transfer, one for the undo
: compute-transfer-quots ( state-in word -- transfer )
    all-type-keys
    [ [ [ compute-key-undo ] keep swap ] 2with H{ } map>assoc ]
    [ [ [ compute-key-transfer ] keep swap ] 2with H{ } map>assoc ] 3bi swap 2array ;

: in>state ( n -- state-in )
    all-type-keys [ swap ?? <array> ] with H{ } map>assoc ;

: xor-merge ( states -- state )
    ! members dup length 1 = [ first ] [ <xor> ] if ;
    [ dup sequence? [ 1array ] unless ] gather
    dup length 1 = [ first ] when ;

:: merge-states ( key-states key -- key-states )
    key-states [ length ] map supremum :> d
    key-states [ d key pad-state ] map
    flip [ xor-merge ] map ;

:: merge-all-states ( states-assoc -- states-assoc )
    all-type-keys
    [| key |
     states-assoc [ key of ] map :> key-states
     key-states key merge-states
     ! ! sequence of states
     ! ! combine stack elements position-wise
     ! key-states [ length ] map supremum :> d
     ! key-states [ d key pad-state ] map
     ! flip [ key type-value-merge ] map
     key swap
    ] H{ } map>assoc ;

ERROR: inferred-divergent-state state-assoc ;
: divergent? ( state-assoc -- ? )
    [ swap [ type-value-diverges? ] curry any? ] assoc-any? ;

: apply-transfers ( state-assoc quot-assoc -- state-assoc )
    [ with-datastack ] assoc-merge
    dup divergent? [ inferred-divergent-state ] when ;

: make-disjunctive-transfer ( quots key -- quot )
    [ dup [ [ inputs ] map supremum ] [ [ outputs ] map supremum ] bi ] dip
    swap '[ _ [ [ output>array ] curry preserving ] map [ _ ndrop ] dip _ merge-states _ firstn ] ;

! ! This is heavy machinery...should infer and build all that at construction time already!!!
! : apply-key-branches ( ..a quots key -- ..b )
!     over
!     [ [ with-datastack ] with map ] dip
!     [ [ type-value-diverges? ] curry reject ]
!     [ merge-states ] bi ; inline

! * Value Ids
! Created for unknown values.  Dup'd values actually have the same id.
! Sets of values constitute disjoint unions.
M: \ value-id unknown-type-value
    counter ;
ERROR: incoherent-split-undo id1 id2 ;
M: \ value-id type-value-undo-dup drop
    2dup = [ drop ] [ incoherent-split-undo ] if ;
! M: \ value-id type-value-merge drop ;
M: \ value-id type-value-undo-merge 2drop ;
M: \ value-id value>type nip counter ;
M: \ value-id apply-declaration 2drop ;
M: \ value-id type-value-diverges? 2drop f ;

! * Class algebra
GENERIC: class-primitive-transfer ( state-in primitive -- transfer-quot/f )
M: object class-primitive-transfer 2drop f ;
! M: \ class unknown-type-value drop ?? ;
! M: \ class type-value-merge drop [ ] [ class-or ] map-reduce ;
M: \ class type-value-undo-merge drop class-and ;
M: \ class type-value-undo-dup drop class-and ;
M: \ class value>type drop <wrapper> ;
M: \ class primitive-transfer
    [ 2dup class-primitive-transfer ] dip swap [ 3nip ] [ call-next-method ] if* ;
! NOTE: assuming that declarations can actually be gradual, we only concretize
! the value here, because the declaration might actually be incomplete...
! NOTE2: actually, concretize both here, the declaration only needs to be
! gradual because we could be able to infer non-gradual declarations

M: \ class apply-declaration drop
    ! [ [ concretize ] dip class-and ] 2map ;
    [ [ concretize ] bi@ class-and ] 2map ;
M: \ class type-value-diverges? drop null = ;

! * Interval computations
! M: \ interval unknown-type-value drop full-interval ;
! M: \ interval type-value-merge drop [ ] [ interval-union ] map-reduce ;
M: \ interval type-value-undo-merge drop interval-intersect ;
! NOTE: backwards assumption propagation creates union behavior here? Is that
! correct?  In case of class, the value could not have disjoint classes to be
! valid in different branches.  However, the same is absolutely not true for intervals...
! TODO: this could be a point to inject polyhedral propagation?
! No, just seems to be wrong...
! M: \ interval type-value-undo-dup drop interval-union ;
M: \ interval type-value-undo-dup drop [ interval-intersect ] or-unknown ;
M: \ interval value>type
    over number? [ drop [a,a] ] [ call-next-method ] if ;
M: \ interval type-value-diverges? drop empty-interval = ;

! TODO: Concretize correctly according to variance!
! In the first approximation, only invariant conversions are safe.
! GENERIC: invariant>interval ( obj type-value-class -- interval )
! M: type-key invariant>interval 2drop ?? ;
! Delegate to classoid value
GENERIC: class-invariant>interval ( classoid -- interval )
! M: \ class invariant>interval
!     drop class-invariant>interval ;

M: classoid class-invariant>interval drop ?? ;
M: math-class class-invariant>interval class-interval ;
M: \ interval apply-declaration drop
    [ class-invariant>interval ] map
    [
        [ interval-intersect ] or-unknown
    ] 2map ;

! * Slots:
! Carry over complete computation history!!!!!!!

! * Relations
! These are going to be hard because we need to be able to transfer them
! locally.
! Could possibly be represented by tuples of relative numbers?
M: \ relation type-value-diverges? 2drop f ;
M: \ relation apply-declaration 2drop ;
