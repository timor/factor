USING: accessors arrays assocs classes classes.algebra combinators effects
kernel math.intervals namespaces quotations sequences stack-checker ;

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
TUPLE: related-values relations ;
SINGLETON: value-id
! INSTANCE: \ literal-value type-key
INSTANCE: \ class type-key
INSTANCE: \ interval type-key
! INSTANCE: \ related-values type-key
INSTANCE: \ value-id type-key

! Hacky...
: all-type-keys ( -- classes )
    type-key class-members [ wrapped>> ] map ;

GENERIC: primitive-transfer ( primitive type-value-class -- transfer-quot )
! NOTE: undos are not assumed to be undoable right now...
GENERIC: primitive-undo ( state-in primitive type-value-class -- undo-quot )

! There is access to a branch-id for identification
: branch-id ( -- id )
    \ branch-id get ;

! Used when undo'ing duplication, i.e. the properties an output value must have to be
! compatible with two different input positions.
! TODO: name correct?

! Combine different outputs
GENERIC: type-value-merge ( outn> type-value-class -- >out )
GENERIC: type-value-undo-merge ( out_i< out< type-value-class -- <out )
GENERIC: type-value-undo-split ( v> <v' type-value-class -- v< )
! GENERIC: type-value-join* ( out1> out2> type-value-class -- >out' )
! ! NOTE: intended for intersection behavior when parallel-execution joins are
! ! propagated backwards
! GENERIC: type-value-undo-join* ( out1> <out' type-value-class -- out1< )
! ! GENERIC: type-value-join* ( x1< x2< x1> type-value-class -- <x1 )
! GENERIC: type-value-meet* ( x1 x2  type-value-class -- x'> )
! ! Default is to assume regular branch-independent reverse fanout.
GENERIC: top-type-value ( type-value-class -- object )
GENERIC: bottom-type-value ( type-value-class -- object )
! Used for inputs
GENERIC: unknown-type-value ( type-value-class -- object )

ERROR: undefined-primitive-type-transfer primitive type-key ;
ERROR: undefined-primitive-type-undo state-in primitive type-key ;

UNION: primitive-data-op \ dup \ drop \ swap ;

M: type-key primitive-transfer
    over primitive-data-op? [ drop 1quotation ]
    [ undefined-primitive-type-transfer ] if ;

: undo-dup ( state-in class -- quot: ( x x -- x ) )
    [ of last ] keep [ type-value-undo-split ] 2curry ;

M: type-key primitive-undo
    { { [ over \ drop eq? ] [ nip of last 1quotation ] }
      { [ over \ swap eq? ] [ 3drop [ swap ] ] }
      { [ over \ dup eq? ] [ nip undo-dup ] }
      [ undefined-primitive-type-undo ]
    } cond ;

ERROR: not-a-primitive-transfer word ;

:: ensure-state-in ( state-in word key -- state-in word key )
    key state-in [
        word stack-effect in>> length
        key unknown-type-value pad-head
    ] changed-at word key ;

: compute-key-transfer ( state-in word key -- quot undo-quot )
    [ ensure-state-in primitive-undo ]
    [ primitive-transfer ] 2bi swap ;

: compute-transfer-quots ( state-in word -- transfer )
    all-type-keys [ [ compute-key-transfer 2array ] keep swap ] 2with H{ } map>assoc ;

! * Value Ids
! Created for unknown values.  Dup'd values actually have the same id.
! Sets of values constitute disjoint unions.
M: \ value-id unknown-type-value
    counter ;
ERROR: incoherent-split-undo id1 id2 ;
M: \ value-id type-value-undo-split drop
    2dup = [ drop ] [ incoherent-split-undo ] if ;
M: \ value-id type-value-merge drop ;
M: \ value-id type-value-undo-merge 2drop ;

! * Class algebra
M: \ class unknown-type-value drop ?? ;
M: \ class type-value-merge drop [ ] [ class-or ] map-reduce ;
M: \ class type-value-undo-merge drop class-and ;
M: \ class type-value-undo-split drop class-and ;

! * Interval computations
M: \ interval unknown-type-value drop full-interval ;
M: \ interval type-value-merge drop [ ] [ interval-union ] map-reduce ;
M: \ interval type-value-undo-merge drop interval-intersect ;
! NOTE: backwards assumption propagation creates union behavior here? Is that
! correct?  In case of class, the value could not have disjoint classes to be
! valid in different branches.  However, the same is absolutely not true for intervals...
! TODO: this could be a point to inject polyhedral propagation?
M: \ interval type-value-undo-split drop interval-union ;
