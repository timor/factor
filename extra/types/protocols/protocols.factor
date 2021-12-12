USING: accessors arrays assocs assocs.extras classes classes.algebra columns
combinators combinators.smart compiler.tree.propagation.info continuations
generalizations generic.math grouping hash-sets kernel kernel.private math
math.intervals namespaces quotations sequences sequences.generalizations sets
types types.bidi types.type-values types.util words ;

IN: types.protocols
! * Type normalization protocols
! Certain type operations expect types to be in a certain shape to be able to
! apply type calculations correctly

! This should provide a coherent set of type coercions.

! Examples:
! - callables need to be cast to effects (arrow types)
! - numeric type calculations are performed on intervals

! * Other approach: modular value info
TUPLE: transfer records transfer-quots undo-quots ;
: transfer-in/out ( transfer -- in out )
    transfer-quots>> values
    [ inputs/outputs 2array ] map <flipped>
    first2 2dup [ all-equal? ] both? [ "unbalanced-branch-transfer" 3array throw ] unless
    [ first ] bi@ ;

C: <transfer> transfer

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

! NOTE: transfers are also not assumed to be undoable right now... As long as
! transitions can be rolled back atomically, that should not be a problem...
GENERIC: primitive-transfer ( state-in primitive domain -- transfer-quot )
! NOTE: undos are not assumed to be undoable right now...
GENERIC: primitive-undo ( state-in primitive domain -- undo-quot )
M: domain value>type 2drop ?? ;

! There is access to a branch-id for identification
: branch-id ( -- id )
    \ branch-id get ;


! UNUSED interesting...
GENERIC: type-values-intersect? ( type-value1 type-value2 domain -- ? )
GENERIC: top-type-value ( domain -- object )

! Used for inputs
M: domain unknown-type-value drop ?? ;

ERROR: undefined-primitive-type-transfer state-in primitive domain ;
ERROR: undefined-primitive-type-undo state-in primitive domain ;

UNION: primitive-data-op \ dup \ drop \ swap \ rot ;

! Pseudo-ops
! SYMBOL: split-control ! ( ..a vals -- ..b branch-vals ) [ split-control ]
! n - number of stack items into branch
! i - branch index
SYMBOL: split> ! ( ..b n i -- ..c )
SYMBOL: >merge   ! ( ..c n -- ..d branch-states )
SYMBOL: merge> ! ( ..d branch-states -- ..e merged )
UNION: control-pseudo-op \ split> \ >merge \ merge> ;

GENERIC: control-transfer-quot ( state-in word domain -- transfer )
GENERIC: control-undo-quot ( state-in word domain -- undo )

: constantly ( value -- quot )
    literalize 1quotation ;

! Thrown by inferred quotations
ERROR: divergent-type-transfer ;

: apply-domain-declaration/check ( domain-value domain-decl domain -- domain-value )
    [ apply-domain-declaration ]
    [ dupd domain-value-diverges? [ divergent-type-transfer ] when ] bi ;

! Declaration is expanded into a spread of per-value domain declaration
! applications.  These are bi-directional bottle-necks.
! Declarations could be seen as the prototypical type-target macro-expansion?
: make-class-declaration-quot ( decls domain -- quot )
    [ class>domain-declaration ] keep
    [ [ apply-domain-declaration/check ] 2curry ] curry
    map [ spread ] curry ;

ERROR: invalid-declaration spec ;

: domain-declaration-transfer ( state-in domain -- quot )
    swap ?last dup [ invalid-declaration ] unless
    class of dup wrapper? [ invalid-declaration ] unless
    wrapped>> swap make-class-declaration-quot ;


M: domain primitive-transfer
    {
        { [ over primitive-data-op? ] [ drop 1quotation nip ] }
        { [ over control-pseudo-op? ] [ control-transfer-quot ] }
        { [ over word? not ] [ value>type constantly nip ] }
        { [ over \ declare eq? ] [ nip domain-declaration-transfer [ drop ]
                                   prepose ] }
        [ undefined-primitive-type-transfer ]
    } cond ;

: undo-dup ( state-in class -- quot: ( x x -- x ) )
    nip '[ 2dup = [ drop ] [  _ type-value-undo-dup ] if ] ;

: drop-saver ( state-in class -- quot )
    [ last ] dip of constantly ;

M: domain primitive-undo
    { { [ over \ drop eq? ] [ nip drop-saver ] }
      { [ over \ swap eq? ] [ 3drop [ swap ] ] }
      { [ over \ dup eq? ] [ nip undo-dup ] }
      { [ over \ rot eq? ] [ 3drop [ -rot ] ] }
      { [ over \ declare eq? ] [ nip
                                 [ domain-declaration-transfer ]
                                 [ drop-saver ] 2bi compose
                               ] }
      { [ over word? not ] [ 3drop [ drop ] ] }
      { [ over control-pseudo-op? ] [ control-undo-quot ] }
      [ undefined-primitive-type-undo ]
    } cond ;

ERROR: not-a-primitive-transfer word ;

: pad-state ( state-in n -- state-in )
    over length -
    dup 0 >
    [ [ <??> ] replicate prepend ]
    [ drop ] if ;

: ensure-state-in ( state-in word -- state-in )
    in-types length pad-state ;

! NOTE: not actually applying declarations here, as that is done during the
! domain-specific transfer.  We only have to ensure there are enough arguments
! on the type stack.
:: ensure-declaration-in ( state-in -- state-in )
    state-in ?last :> spec
    spec class of wrapper? [ spec invalid-declaration ] unless
    spec class of wrapped>> :> spec
    spec length :> n
    state-in n 1 + pad-state
    ! state-in unclip-last-slice :> ( value-state decl-type-value )
    ! value-state n pad-state
    ! spec apply-declaration
    ! decl-type-value suffix
    ;

! Interface function
! Used to ensure that undo and transfer functions have correct setup
: empty-state ( -- state-in )
    f ;

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

ERROR: inferred-divergent-state state ;
: divergent? ( state -- ? )
    [ divergent-type-value? ] any? ;

! Apply a transfer assoc to the state.  Check if any of the resulting states are divergent ;
: apply-transfers ( state quot-assoc -- state )
    with-domain-stacks
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

: split-intro ( n i dom -- quot: ( in> -- >in ) )
    ! [ type-value-perform-split ] 2curry <repetition>
    ! [ spread ] curry ;
    3drop [  ] ;

SINGLETON: +bottom+
: collect-outro ( quot outn -- quot: ( ..a n -- ..b values' ) )
    over '[ [ @ _ narray ]
            [ dup divergent-type-transfer?
              [ drop _ nullary +bottom+ ]
              [ rethrow ] if
            ] recover
    ] ;

! : collect-outro ( quot n -- quot: ( ..a n -- ..b values' ) )
!     '[ @ _ narray ] ;

: augment-branch-transfer-quot ( branch-quot in out i dom -- quot )
    rot
    [ split-intro prepose ] dip
    collect-outro
    ;

: augment-branch-transfer-quots ( quots in out dom -- quots )
    '[ _ _ rot _ augment-branch-transfer-quot ] map-index ;

: parallelize ( quots in -- quot: ( ..a -- ..b branch-values ) )
    '[ _ [ preserving ] map [ _ ndrop ] dip ] ;

: parallel>collect ( branch-quots in out dom -- quot )
    pick [ augment-branch-transfer-quots ] dip
    parallelize  ;

: combine-push ( out quot: ( type-values -- type-value ) -- quot )
    swap
    '[ [ +bottom+? ] reject <flipped> _ map _ firstn ] ;

: parallel>merge ( branch-quots in out dom -- quot )
    [ parallel>collect ] 2keep
    '[ _ type-value-merge ] combine-push compose ;

: all-parallel>merge ( transfers -- quots-assoc )
    [| dom transfers |
     transfers dup first transfer-in/out :> ( in out )
     [ transfer-quots>> dom of ] map in out dom parallel>merge
    ] curry map-domains ;

! ** Undo parallel-transfer
: check-divergence ( value domain -- value )
    dupd domain-value-diverges?
    [ divergent-type-transfer throw ] when ;


! This is a runtime version of declare that performs the type intersection
! operation and throws an error if a null value has been obtained.
: mask-undo-split ( domain-values domain -- quot: ( ..a -- ..b ) )
    [ [ [ type-value-undo-merge ] [ check-divergence ] bi ] 2curry ] curry
    map [ spread ] curry ;

! : collect-undo-outro ( quot outn -- quot: ( ..a n -- ..b values' ) )
!     over '[ [ @ _ narray ]
!        [ dup divergent-type-transfer?
!          [ drop _ nullary +bottom+ ]
!          [ rethrow ] if
!        ] recover
!     ] ;

: augment-branch-undo-quot ( undo-out branch-quot branch-state dom -- quot )
    mask-undo-split prepose swap collect-outro ;

: parallel<collect ( branch-quots branch-states undo-out undo-in dom -- quot )
    swap [ [ [ -rot ] dip augment-branch-undo-quot ] 2curry 2map ] dip
    parallelize
    ;

: parallel<unsplit ( branch-quots branch-states undo-out undo-in dom -- quot )
    [ parallel<collect ] 3keep nip
    '[ _ type-value-undo-split ] combine-push compose ;

! For the undo direction, we need the same thing but use the stored outputs of the
! already inferred branch transfer as a mask to synthesize a declaration that
! ensures that the branch will cut out as much disjunction information as possible.
! For each domain, there is a sequence of undo quotations.  For each undo
! quotation, we need to insert the domain declarations separately.

! transfers
! { transfer1{ records... undo-quots... }
!   transfer2{ records... undo-quots... } }
: all-parallel<unsplit ( out-states transfers -- quots-assoc )
    [| dom branch-states branch-transfers |
     branch-states [ [ dom of ] map ] map :> domain-states
     branch-transfers dup first transfer-in/out :> ( out in )
     [ undo-quots>> dom of ] map domain-states out in dom
     parallel<unsplit
    ] 2curry map-domains ;

! * Value Ids
! Created for unknown values.  Dup'd values actually have the same id.
! Sets of values have conjunctive behavior, i.e. whatever is there has been part
! of these values.
! For unknown values we create an id but also leave the unknown type.  This
! ensures that we can propagate different values along later-on.
M: \ value-id unknown-type-value
    counter <scalar> ?? 2array >hash-set ;
ERROR: incoherent-split-undo id1 id2 ;
M: \ value-id type-value-undo-dup drop
    2dup = [ drop ] [ incoherent-split-undo ] if ;
M: \ value-id type-value-merge drop union-all ; ! NOTE: ?? is not a top value of the lattice.
M: \ value-id type-value-undo-split type-value-merge ;
M: \ value-id type-value-undo-merge drop intersect ;
M: \ value-id value>type nip counter <scalar> 1array >hash-set ;
M: \ value-id apply-class-declaration 2drop ;
M: \ value-id domain-value-diverges?* drop null? ;
M: \ value-id type-value-perform-split drop
    [ members ] dip [ <branched> ] curry map >hash-set ;
M: \ value-id class>domain-declaration drop ;
M: \ value-id apply-domain-declaration 2drop ;

! * Class algebra
GENERIC: class-primitive-transfer ( state-in primitive -- transfer-quot/f )
M: object class-primitive-transfer 2drop f ;
M: \ class type-value-merge drop [ ] [ class-or ] map-reduce ;
M: \ class type-value-undo-merge drop class-and ;
M: \ class type-value-undo-dup drop [ class-and ] and-unknown ;
M: \ class value>type drop <wrapper> ;
M: \ class primitive-transfer
    [ 2dup class-primitive-transfer ] dip swap [ 3nip ] [ call-next-method ] if* ;

! NOTE: Concretization necessary here?
M: \ class apply-class-declaration drop
    [ [ class-and ] and-unknown ] 2map-suffix ;
M: \ class domain-value-diverges?* drop null = ;
M: \ class bottom-type-value drop null ;
M: \ class type-value-undo-split type-value-merge ;
M: \ class class>domain-declaration drop ;
M: \ class apply-domain-declaration drop
    [ class-and ] and-unknown ;

! * Interval computations
M: \ interval type-value-merge drop [ ] [ [ interval-union ] or-unknown ] map-reduce ;
M: \ interval type-value-undo-merge drop [ interval-intersect ] and-unknown ;
! NOTE: backwards assumption propagation creates union behavior here? Is that
! correct?  In case of class, the value could not have disjoint classes to be
! valid in different branches.  However, the same is absolutely not true for intervals...
! TODO: this could be a point to inject polyhedral propagation?
! No, just seems to be wrong...
! M: \ interval type-value-undo-dup drop interval-union ;
M: \ interval type-value-undo-dup drop [ interval-intersect ] and-unknown ;
M: \ interval value>type
    over number? [ drop [a,a] ] [ call-next-method ] if ;
M: \ interval domain-value-diverges?* drop empty-interval = ;
M: \ interval type-value-undo-split
    type-value-merge ;


! TODO: Concretize correctly according to variance!
! In the first approximation, only invariant conversions are safe.
! GENERIC: invariant>interval ( obj domain -- interval )
! M: domain invariant>interval 2drop ?? ;
! Delegate to classoid value
GENERIC: class-invariant>interval ( classoid -- interval )

M: classoid class-invariant>interval drop ?? ;
M: math-class class-invariant>interval class-interval ;
M: wrapper class-invariant>interval wrapped>>
    interval value>type ;
M: \ interval class>domain-declaration drop
    [ class-invariant>interval ] map ;
M: \ interval apply-domain-declaration drop
    [ interval-intersect ] and-unknown ;
M: \ interval apply-class-declaration
    [ class>domain-declaration ] keep
    '[
        _ apply-domain-declaration
        ! [ interval-intersect ] and-unknown
    ] 2map-suffix ;

! * Slots:
! Carry over complete computation history!!!!!!!

! ! * Relations
! ! These are going to be hard because we need to be able to transfer them
! ! locally.
! ! Could possibly be represented by tuples of relative numbers?
! M: \ relation domain-value-diverges?* 2drop f ;
! M: \ relation apply-class-declaration 2drop ;
