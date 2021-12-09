USING: accessors arrays assocs assocs.extras classes classes.algebra columns
combinators combinators.smart compiler.tree.propagation.info continuations
generalizations generic.math grouping kernel kernel.private math math.intervals
namespaces quotations sequences sequences.generalizations sets types types.bidi
types.type-values types.util words ;

IN: types.protocols
! * Type normalization protocols
! Certain type operations expect types to be in a certain shape to be able to
! apply type calculations correctly

! This should provide a coherent set of type coercions.

! Examples:
! - callables need to be cast to effects (arrow types)
! - numeric type calculations are performed on intervals

! * Other approach: modular value info
! quots are a hashtable of orthogonal lattices that are traversed in parallel,
! each entry having two elements, a forward and a backwards quot.
! Known lattice keys:
! literal
! class
! interval
! slot-access?

! Protocol:
! For each domain we need: bottom and top value,
! Conversion from class
! Conversion from value
! Meet and join operations?
! (Least) upper bound: join
! (Greatest) lower bound: meet

! Domains must be independent.  Information of different states may only
! combined to decide on what code to generate next.  This is some form of
! independence guarantee so it does not matter whether we compute the compound
! of a word or its constituents.

TUPLE: literal-value value ;
! TUPLE: class-value class ;
! TUPLE: interval-value interval ;
! TUPLE: relation value ;
! TUPLE: eql-to < relation ;
! TUPLE: less-than < relation ;
! TUPLE: greater-than < relation ;
! INSTANCE: \ literal-value domain
! INSTANCE: \ relation domain

! NOTE: transfers are also not assumed to be undoable right now... As long as
! transitions can be rolled back atomically, that should not be a problem...
GENERIC: primitive-transfer ( state-in primitive domain -- transfer-quot )
! NOTE: undos are not assumed to be undoable right now...
GENERIC: primitive-undo ( state-in primitive domain -- undo-quot )
M: domain value>type 2drop ?? ;

! There is access to a branch-id for identification
: branch-id ( -- id )
    \ branch-id get ;


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
! Backprop merged into exclusive control-paths
! XXX
! M: domain type-value-undo-merge drop <and> ;
GENERIC: type-values-intersect? ( type-value1 type-value2 domain -- ? )
! Re-Combination of data-path-split
GENERIC: type-value-undo-dup ( v> <v' domain -- v< )
! Backprop into common history of exclusive control-paths
! GENERIC: type-value-undo-split ( v> <out )
! GENERIC: type-value-join* ( out1> out2> domain -- >out' )
! ! NOTE: intended for intersection behavior when parallel-execution joins are
! ! propagated backwards
! GENERIC: type-value-undo-join* ( out1> <out' domain -- out1< )
! ! GENERIC: type-value-join* ( x1< x2< x1> domain -- <x1 )
! GENERIC: type-value-meet* ( x1 x2  domain -- x'> )
! ! Default is to assume regular branch-independent reverse fanout.
GENERIC: top-type-value ( domain -- object )
GENERIC: bottom-type-value ( domain -- object )
! Used for inputs
M: domain unknown-type-value drop ?? ;

ERROR: undefined-primitive-type-transfer state-in primitive domain ;
ERROR: undefined-primitive-type-undo state-in primitive domain ;

UNION: primitive-data-op \ dup \ drop \ swap \ rot ;

: constantly ( value -- quot )
    literalize 1quotation ;

M: domain primitive-transfer
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

M: domain primitive-undo
    { { [ over \ drop eq? ] [ nip of last constantly ] }
      { [ over \ swap eq? ] [ 3drop [ swap ] ] }
      { [ over \ dup eq? ] [ nip undo-dup ] }
      { [ over \ rot eq? ] [ 3drop [ -rot ] ] }
      { [ over word? not ] [ 3drop [ drop ] ] }
      [ undefined-primitive-type-undo ]
    } cond ;

ERROR: not-a-primitive-transfer word ;

: pad-state ( state-in n -- state-in )
    over length -
    dup 0 >
    [ [ <??> ] replicate prepend ]
    [ drop ] if ;

! :: ensure-state-in ( state-in word -- state-in )
!     word in-types length :> n
!     state-in [| state |
!         state n pad-state
!     ] map ;

: ensure-state-in ( state-in word -- state-in )
    in-types length pad-state ;
    ! state-in [| state |
    !     state n pad-state
    ! ] map ;

ERROR: invalid-declaration spec ;
:: ensure-declaration-in ( state-in -- state-in )
    state-in ?last :> spec
    spec wrapper? [ spec invalid-declaration ] unless
    spec wrapped>> :> spec
    spec length :> n
    state-in unclip-last-slice :> ( value-state decl-type-value )
    value-state [
        spec apply-declaration
    ] map
    decl-type-value suffix ;

! Interface function
! Used to ensure that undo and transfer functions have correct setup
: empty-state ( -- state-in )
    f ;
    ! all-domains [ { } ] H{ } map>assoc ;

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
    all-domains
    [ [ [ compute-key-undo ] keep swap ] 2with H{ } map>assoc ]
    [ [ [ compute-key-transfer ] keep swap ] 2with H{ } map>assoc ] 3bi swap 2array ;

: in>state ( n -- state-in )
    all-domains [ swap ?? <array> ] with H{ } map>assoc ;

: xor-merge ( states -- state )
    ! members dup length 1 = [ first ] [ <xor> ] if ;
    [ dup sequence? [ 1array ] unless ] gather
    dup length 1 = [ first ] when ;

: merge-states ( list-of-list-of-type-values -- list-of-type-values )
    dup [ length ] <mapped> all-equal? [ "unbalanced-states" 2array throw ] unless
    <flipped> [ concat members ] map flip ;

ERROR: inferred-divergent-state state ;
: divergent? ( state -- ? )
    ! [ swap [ domain-value-diverges?* ] curry any? ] assoc-any? ;
    [ divergent-type-value? ] any? ;

: apply-transfers ( state quot-assoc -- state )
    with-domain-stacks
    ! [ with-domain ] assoc-merge
    dup divergent? [ inferred-divergent-state ] when ;

! ** Forward-parallel-transfer
! The problem is that we have to leave the first-class environment here and
! trampoline up.  Since the transfer itself has been performed already, we know:
! - The input state of the transfer
! - The output state of the transfer
! - The transition sequence of the transfer

! What we don't know is the exact depth it has accessed.  We can infer this from
! the accumulated transfer quotation though.

! Assuming an inferred branch transfer quotation :q ( ..a -- ..b ) with input
! number i and output number o.

! Build a trampoline quotation which calls q and collects the output, but leaves
! the inputs on the stack.

! Do this for all branch transfers.
! Then build a cleave sequence, which in turn accumulates all the corresponding
! output stacks, drop the inputs, push the sequences and call the merger.

: parallel>merge ( quots -- quot )
    dup [ [ inputs ] map supremum ] [ [ outputs ] map supremum ] bi
    '[ _ [ [ output>array ] curry preserving ] map [ _ ndrop ] dip merge-states _ firstn ] ;


! This is a runtime version of declare that performs the type intersection
! operation and throws an error if a null value has been obtained.
: declare-value-type ( declaration -- )
    [  ] !

! For the undo direction, we need the same thing but use the stored outputs of the
! already inferred branch transfer as a mask to synthesize a declaration that
! ensures that the branch will cut out as much disjunction information as possible.
! For each domain, there is a sequence of undo quotations.  For each undo quotation
: parallel<merge ( states quots -- quot )




! ! This is heavy machinery...should infer and build all that at construction time already!!!
! : apply-key-branches ( ..a quots key -- ..b )
!     over
!     [ [ with-datastack ] with map ] dip
!     [ [ domain-value-diverges?* ] curry reject ]
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
M: \ value-id apply-domain-declaration 2drop ;
M: \ value-id domain-value-diverges?* 2drop f ;

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

M: \ class apply-domain-declaration drop
    ! [ [ concretize ] dip class-and ] 2map ;
    [ [ concretize ] bi@ class-and ] 2map ;
M: \ class domain-value-diverges?* drop null = ;

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
M: \ interval domain-value-diverges?* drop empty-interval = ;

! TODO: Concretize correctly according to variance!
! In the first approximation, only invariant conversions are safe.
! GENERIC: invariant>interval ( obj domain -- interval )
! M: domain invariant>interval 2drop ?? ;
! Delegate to classoid value
GENERIC: class-invariant>interval ( classoid -- interval )
! M: \ class invariant>interval
!     drop class-invariant>interval ;

M: classoid class-invariant>interval drop ?? ;
M: math-class class-invariant>interval class-interval ;
M: \ interval apply-domain-declaration drop
    [ class-invariant>interval ] map
    [
        [ interval-intersect ] or-unknown
    ] 2map ;

! * Slots:
! Carry over complete computation history!!!!!!!

! ! * Relations
! ! These are going to be hard because we need to be able to transfer them
! ! locally.
! ! Could possibly be represented by tuples of relative numbers?
! M: \ relation domain-value-diverges?* 2drop f ;
! M: \ relation apply-domain-declaration 2drop ;
