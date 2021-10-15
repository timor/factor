USING: accessors arrays assocs classes.tuple combinators
combinators.short-circuit compiler.tree.propagation.info grouping hashtables
kernel math math.intervals namespaces sequences sets sorting strings terms
types.algebra ;

IN: types.base-types

FROM: namespaces => set ;

! * Atomic type variables and Primitives
TUPLE: type-var
    { name string read-only }
    { id integer read-only }
    { order integer read-only } ;

: <type-var> ( name id -- obj )
    0 type-var boa ;

: type-var-key ( type-var -- key )
    [ name>> ] [ id>> ] bi 0 type-var boa ;

GENERIC: change-type-var-order ( amount term -- term )
PREDICATE: base-type-var < type-var order>> 0 = ;
PREDICATE: dup-type-var < type-var order>> 0 > ;
! INSTANCE: base-type-var term-var
INSTANCE: type-var term-var
! INSTANCE: dup-type-var proper-term
! M: dup-type-var args>> drop f ;

! TUPLE: unique-var < type-var
!     { name string read-only } ;

! INSTANCE: unique-var term-var
: <unique-var> ( -- obj )
    "U" \ <unique-var> counter <type-var> ;
: <unique-named-var> ( type-var -- obj )
    \ <unique-var> counter <type-var> ;
: base-var= ( type-var1 type-var2 -- ? )
    { [ [ name>> ] bi@ = ]
      [ [ id>> ] bi@ = ]
    } 2&& ;

! Matches wrong order, need to correct replacement
! M: type-var occurs-free?
!     base-var= ;

! : shift-term-non-recursive? ( replacement-term target-var eliminated-var -- ? )
!     { [ drop swap occurs-free? not ]
!     } 3&& ;

! : shift-term-recursive? ( replacement-term target-var eliminated-var -- ? )
!     { [ drop swap occurs-free? ]
!       [ [ order>> ] bi@ >= nip ]
!     } 3&& ;

! SYMBOL: shifting?

! GENERIC: shift-vars ( except amount term -- term )
! M: type-var shift-vars
!     rot dupd in?
!     [ nip ] [ change-type-var-order ] if ;
! M: proper-term shift-vars
!     [ shift-vars ] 2with map-args ;

! : shift-non-recursive ( amount replacement-term -- term )
!     [ f ] 2dip shift-vars ;

! ! Two steps:
! ! 1. shift all vars except for the one we are replacing
! ! 2. substitute the old term into the var
! : shift-step-recursive ( replacement-term var -- term )
!     swap
!     [ [ 1array 1 ] dip shift-vars ]
!     [ shifting? [ subst-in-term ] with-variable-on ] 2bi ;

! : shift-term-recursive ( replacement-term target-var eliminated-var -- term )
!     [ [ order>> ] bi@ - ] keep swap
!     [ shift-step-recursive ] with times ;

! ! FIXME: Can obviously directly count up
! : shift-term-non-recursive ( replacement-term target-var eliminated-var -- term )
!     [ order>> ] bi@ - swap shift-non-recursive ;

! ! Handling replacements
! : lift-order-var ( target-term-var eliminated-type-var replacement-term -- term )
!     -rot {
!         { [ 2dup = ] [ 2drop ] } ! NOTE: redundant, same as shift=0 (except for recursion check!)
!         { [ 3dup shift-term-recursive? ] [ shift-term-recursive ] }
!         { [ 3dup shift-term-non-recursive? ] [ shift-term-non-recursive ] }
!         [ 2drop ]
!     } cond ;

! : substitution-match? ( subst term -- term alist )
!     swap over [ base-var= ] curry filter-keys
!     dup assoc-size 1 > [ "huh?" throw ] when
!     >alist ;

! M: type-var lift* ( subst term -- term )
!     substitution-match?
!     [ first first2
!       shifting? get
!       [ 2nip ]
!       [ lift-order-var ] if
!     ] unless-empty
!     ;

TUPLE: type-const thing ;
C: <type-const> type-const
INSTANCE: type-const proper-term
M: type-const args>> drop f ;
M: type-const change-type-var-order nip ;

M: type-const term-value-type thing>> ;

PREDICATE: f-type < type-const thing>> \ f = ;
: <f-type> ( -- type ) \ f <type-const> ;

TUPLE: dup-type element ;
C: <dup-type> dup-type
INSTANCE: dup-type proper-term
M: dup-type args>> element>> 1array ;
M: dup-type from-args* drop
    first <dup-type> ;
! M: dup-type lift*
!     element>> lift*
!     <dup-type> ;
! M: dup-type occurs-free? 2drop f ;

! Syntax type
SINGLETON: +drop+
PREDICATE: +drop+-type < type-const thing>> +drop+? ;

! type-term
GENERIC: propagate-drop ( term -- term )
TUPLE: drop-type element ;
INSTANCE: drop-type proper-term
! INSTANCE: drop-type term-var
C: <drop> drop-type
M: drop-type args>> element>> 1array ;
M: drop-type from-args*
    drop first <drop> ;
! M: drop-type lift*
!     lift* propagate-drop ;
    ! swap dupd at
    ! [ nip ] when* ;

M: type-var change-type-var-order
    swap [ [ name>> ] [ id>> ] [ order>> ] tri ] dip
    + type-var boa ;

M: type-var propagate-drop
    <drop> ;

M: type-const propagate-drop ;

PREDICATE: dup-var < dup-type element>> type-var? ;
INSTANCE: dup-var term-var

TUPLE: rec-type { rec-var maybe{ term-var string } } element ;
C: <rec-type> rec-type
INSTANCE: rec-type proper-term
! ! ERROR: rec-type-has-no-args rec-type ;
M: rec-type args>> [ rec-var>> ] [ element>> ] bi 2array ;
M: rec-type from-args* drop first2
    <rec-type> ;
: abstract-rec-type ( rec-var term -- term )
    [ <unique-var> swap dupd associate ] dip lift*
    <rec-type> ;
! NOTE: two choices here: either make new variables, or simply unfold
! For now, simply unfold...
: instantiate-rec-type ( arg-term rec-type -- lhs rhs )
    dupd [ rec-var>> associate ] [ element>> ] bi lift* ;

M: rec-type occurs-free?
    { [ rec-var>> = ] [ element>> occurs-free? not ] } 2||
    not ;
! ERROR: cannot-dup-recursive-type rec-type ;
! M: rec-type change-type-var-order cannot-dup-recursive-type ;
! ! Note: only free args!
! M: rec-type lift*
!     [ [ clone >hashtable ] dip
!       [ rec-var>> over delete-at ] [ element>> ] bi
!       lift* ]
!     [ rec-var>> ] bi swap <rec-type> ;

! : should-lower-order? ( dropped-type-var type-var -- ? )
!     { [ base-var= ]
!       [ [ order>> ] bi@ < ]
!     } 2&& ;

! GENERIC: lower-var-orders ( type-var term -- term )
! M: type-var lower-var-orders
!     2dup should-lower-order?
!     [ -1 swap change-type-var-order ] when
!     nip ;
! M: proper-term lower-var-orders
!     [ lower-var-orders ] with map-args ;

GENERIC: change-term-var-orders ( amount type-var term -- term )
M: type-var change-term-var-orders
    2dup base-var=
    [ nip change-type-var-order ]
    [ 2nip ] if ;

M: type-var term-value-type drop object ;

M: proper-term change-term-var-orders
   [ change-term-var-orders ] 2with map-args ;

! * Pred/Succ constructors

TUPLE: pred-type element ;
C: <pred> pred-type
INSTANCE: pred-type proper-term
M: pred-type args>> element>> 1array ;
M: pred-type from-args* drop first <pred> ;
TUPLE: succ-type element ;
C: <succ> succ-type
INSTANCE: succ-type proper-term
M: succ-type args>> element>> 1array ;
M: succ-type from-args* drop first <succ> ;

UNION: PS pred-type succ-type ;

GENERIC: simplify-psd ( term -- term )
GENERIC: propagate-pred ( term -- term )
M: term-var propagate-pred <pred> ;
M: proper-term propagate-pred
    [ propagate-pred ] map-args ;
M: pred-type lift*
    element>> lift* <pred>
    simplify-psd
    ;
!     ! element>> lift*
!     dup { [ drop-type? ] [ succ-type? ] } 1||
!     [ element>> ]
!     [ propagate-pred ] if ;
! M: drop-type propagate-pred <pred> ;
! M: term propagate-pred <pred> ;

GENERIC: propagate-succ ( term -- term )
M: term-var propagate-succ <succ> ;
M: proper-term propagate-succ
    [ propagate-succ ] map-args ;
M: succ-type lift*
    element>> lift* <succ>
    simplify-psd
    ;
    ! element>> lift*
    ! dup { [ drop-type? ] [ pred-type? ] } 1||
    ! [ element>> ]
    ! [ propagate-succ ] if ;
! M: term propagate-succ <succ> ;
! M: drop-type propagate-succ <succ> ;

! This collects constraints between variables of different orders
: var-orders ( term -- assoc )
    term-vars [ type-var-key ] collect-by ;
: var-order-pairs ( seq -- seq )
    [ order>> ] sort-with 2 <clumps> ;
: var-order-constraints ( seq -- eqns )
    var-order-pairs
    [ first2
      [ <pred> 2array
        ! Dropping this makes call work
        ! Dropping this also makes swap work
        ! Same with nip
        ! Having both seems to need distribution for swap
      drop f
      ]
      [ [ <succ> ] dip swap 2array
        ! NOTE: dropping this for now
        ! Dropping this also makes call work
        ! Dropping this makes swap work
        ! Same with nip here
        ! drop f
      ] 2bi
      2array
    ] map concat
    sift
    ;
: get-constraints ( term -- assoc )
    var-orders values [ var-order-constraints ] map concat ;
    ! term-vars [ { [ type-var? ] [ order>> 0 > ] } 1&& ] filter
    ! [ dup -1 swap change-type-var-order
    !   ! [ <succ> 2array ]
    !   ! [ [ <pred> ] dip swap 2array ] 2bi
    !   ! 2array
    !   [ <pred> ] dip swap 2array
    !   ! <succ> 2array
    !   1array
    ! ] map concat ;

! ** Simplification
M: term simplify-psd ;
M: proper-term simplify-psd
    [ simplify-psd ] map-args ;

! NOTE: currently implementing different handling of SD and PD here!
! NOTE NOTE: nope, doing same in both again, since there was an error masked before
! SPx = x
! SDx = Sx
! Sfoo = Sfoo
M: succ-type simplify-psd
    element>> simplify-psd
    ! dup { [ pred-type? ] [ drop-type? ] } 1||
    dup pred-type?
    [ element>> ]
    [ dup drop-type?
      [ element>> <succ> ]
      [ <succ> ] if ] if ;

M: pred-type simplify-psd
    element>> simplify-psd
    dup { [ succ-type? ] [ drop-type? ] } 1||
    [ element>> ]
    [ dup drop-type?
      [ element>> <pred> ]
      [ <pred> ] if ] if ;

M: drop-type simplify-psd
    element>> simplify-psd
    ! dup pred-type?
    dup PS?
    [ element>> ] [ <drop> ] if ;

! ** Normalize drop types
GENERIC: collect-drops* ( seq drop? term -- seq )
M: proper-term collect-drops*
    [ collect-drops* ] with each-arg ;
M: term collect-drops* 2drop ;
M: drop-type collect-drops*
    [ drop t ] dip element>> collect-drops* ;
M: term-var collect-drops*
    -rot swapd [ suffix ] [ drop ] if ;

: collect-drops ( term -- seq )
    [ { } f ] dip collect-drops* ;

: eliminate-drop ( term var -- term )
    [ <pred> ] keep associate swap lift* ;

: eliminate-drop-step ( term -- term changed? )
    dup collect-drops members
    [ f ]
    [ [ eliminate-drop ] each
      simplify-psd
      t ] if-empty ;

: eliminate-drop-terms ( term -- term )
    [ eliminate-drop-step ] loop ;

! ** Conversion to ordered variables
! Non-normalizing
GENERIC: convert-to-vars ( term -- term )
M: pred-type convert-to-vars
    element>> convert-to-vars
    dup type-var?
    [ -1 swap change-type-var-order ]
    [ <pred> ] if
    ;
M: succ-type convert-to-vars
    element>> convert-to-vars
    dup type-var?
    [ 1 swap change-type-var-order ]
    [ <succ> ] if
    ;
M: proper-term convert-to-vars
    [ convert-to-vars ] map-args ;
M: term convert-to-vars ;

! Normalizing
GENERIC: reconvert-to-vars ( mapping level term -- mapping term )
M:: type-var reconvert-to-vars ( mapping level term -- mapping term )
    term type-var-key mapping [ ] cache
    [ name>> ] [ id>> ] bi level type-var boa
    mapping swap
    ;
M: proper-term reconvert-to-vars
    [ reconvert-to-vars ] with map-args ;
M: succ-type reconvert-to-vars
    [ 1 + ] [ element>> ] bi* reconvert-to-vars ;
M: pred-type reconvert-to-vars
    [ 1 - ] [ element>> ] bi* reconvert-to-vars ;
! M: unique-var reconvert-to-vars nip ;

: eliminate-pred/succ ( term -- term )
    [ H{ } clone 0 ] dip reconvert-to-vars nip ;

! * Input instantiation
! This is used to capture the notion that input quotations can be different
! instances, yet must match the same type.  When unifying, the alternatives are
! instantiated with fresh variables on the other side
! TODO: check if there is need to distinguish what is instantiated

! Intersection behavior
TUPLE: sum-type alternatives ;
C: <sum-type> sum-type
INSTANCE: sum-type proper-term
M: sum-type args>> alternatives>> ;
M: sum-type from-args* drop <sum-type> ;
M: sum-type simplify-term*
    call-next-method
    dup alternatives>> all-equal?
    [ alternatives>> first [ drop t ] dip ] when ;

: new-var-substitution ( term -- assoc )
    term-vars members [ dup 1 swap change-type-var-order ] H{ } map>assoc ;

GENERIC: instantiate-term ( term -- term )

! NOTE: highly experimental.  We instantiate something, thus assuming nothing
! about the types!
! Doesnt seem to be correct, actually
! M: type-const instantiate-term drop <unique-var> ;

M: proper-term instantiate-term
    [ new-var-substitution ]
    [ lift* ] bi ;

: instantiate1 ( template term -- template' instance term )
    [ [ instantiate-term ] keep ] dip ;

: instantiate-bound-vars ( term vars -- term )
    [ dup name>> <unique-named-var> ] H{ } map>assoc
    swap lift* ;

: free-var-substitutions ( vars -- copy1-subst copy2-subst problem-subst )
    dup [ [ dup name>> <unique-named-var> ] { } map>assoc ] bi@
    2dup [ [ first2 ] [ second ] bi* 2array <sum-type> 2array ] 2map ;

: instantiate-copies ( term -- term1 term2 subst )
    dup dup bound/free-vars
    [ [ instantiate-bound-vars ] curry bi@ ] dip
    free-var-substitutions
    [ swapd [ swap lift* ] 2bi@ ] dip ;

: instantiate-alternatives ( term sum-type -- pairs )
    swap [ alternatives>> first2 ] dip instantiate-copies
    [ swapd [ 2array ] 2bi@ 2array ] dip prepend ;

! : instantiate-alternatives ( term alternatives -- pairs )
!     alternatives>> [ instantiate1 2array ] map nip ;

! * Conditional type

TUPLE: conditional-type condition type ;
INSTANCE: conditional-type proper-term
M: conditional-type args>> [ condition>> ] [ type>> ] bi 2array ;

! This is probably already a form of dependent type, although pretty much the
! simplest one I can think of: This type will desugar into +any+ iff the
! condition is = f
TUPLE: maybe-type < conditional-type ;
C: <maybe-type> maybe-type
INSTANCE: maybe-type proper-term
M: maybe-type from-args* drop first2 <maybe-type> ;

TUPLE: subtype typee supertype ;
C: <subtype> subtype
INSTANCE: subtype proper-term
M: subtype args>> [ typee>> ] [ supertype>> ] bi 2array ;
M: subtype from-args* drop first2 <subtype> ;


! NOTE: this is a bad name, and also not a sum type
! Disjoint union behavior
TUPLE: all-type < sum-type ;
C: <all-type> all-type
M: all-type from-args* drop <all-type> ;

TUPLE: choice-type cond then else ;
C: <choice-type> choice-type
INSTANCE: choice-type proper-term
: simplify-choice-condition ( changed? choice -- changed? choice )
    dup cond>>
    { { [ dup t <type-const> term-types-intersect? not ]
        [ drop else>> [ drop t ] dip ] }
      { [ dup <f-type> term-types-intersect? not ]
        [ drop then>> [ drop t ] dip ] }
      [ drop ]
    } cond ;

: simplify-identical-choice ( changed? choice -- changed? choice )
    dup [ then>> ] [ else>> ] bi =
    [ else>> [ drop t ] dip ] when ;

M: choice-type simplify-term*
    call-next-method
    dup choice-type? [ simplify-choice-condition ] when
    dup choice-type? [ simplify-identical-choice ] when
    ;


! * Variance
TUPLE: variant-type type ;
: new-variant ( type class -- obj ) new swap >>type ;

INSTANCE: variant-type term-var
M: variant-type args>> type>> 1array ;

! ! Interestingly, when thinking only of functions, then lhs and rhs directly
! ! corresponds to contravariant-type and covariant, respectively.
! TUPLE: covariant-type < variant-type ;
! C: <covariant> covariant-type
! M: covariant-type from-args* drop
!     first <covariant> ;

! TUPLE: contravariant-type < variant-type ;
! C: <contravariant> contravariant-type
! M: contravariant-type from-args* drop
!     first <contravariant> ;

! TUPLE: invariant-type < variant-type ;
! C: <invariant> invariant-type
! M: invariant-type from-args* drop
!     first <invariant> ;

! GENERIC: make-variant ( class type -- type )
! M: proper-term make-variant
!     [ make-variant ] with map-args ;
! M: term-var make-variant
!     swap new-variant ;
SINGLETONS: +in+ +co+ +contra+ ;
UNION: variance +in+ +co+ +contra+ ;
GENERIC: type-variance ( proper-term -- seq )
M: proper-term type-variance
    args>> length +in+ <array> ;

! * Annotations
! Elimination of annotations: When substituting into a target, the annotations
! have to be merged.  E.g. elim ( .. vname term -- term ) is called with vname
! being a possibly annotated term-var, and term being the thing that is
! replaced.  Note that we need to keep track of the variance, i.e. the resulting
! annotation can be different for the same variable, depending on which position
! it is in.

! ! Annotations is an assoc from annotation class to annotation value
! TUPLE: annotated-term-var < term-var type-var annotations ;
! GENERIC: lift-annotation ( source-variance variable-variance variable term-variance term )

! * Data types


! ** Symbolic computation
! INSTANCE: value-info-state proper-term ;

! In addition to the type constants, these are actual types which represent
! values other than words to be executed.
! Base type for representing maps and sequences alike
! TUPLE: entry key value ;
! INSTANCE: entry proper-term ;
! TUPLE: record-type { mappings list } ;
! INSTANCE: record-type proper-term


! Partial constructor
! During unification, this must actually match against stack elements.  Problem:
! we only know that this
! TUPLE: tuple-type class { slots list } ;
! INSTANCE: tuple-type proper-term

! ** Complex types
INSTANCE: value-info-state proper-term
INSTANCE: interval proper-term

TUPLE: sequence-type length-type element-type ;
C: <sequence-type> sequence-type
INSTANCE: sequence-type proper-term

! Declared tuple type, non-parametric
TUPLE: tuple-type class slot-types ;
C: <tuple-type> tuple-type
INSTANCE: tuple-type proper-term
M: tuple-type args>> slot-types>> ;
M: tuple-type from-args* class>> swap <tuple-type> ;
M: tuple-type type-variance
    class>> all-slots [ read-only>> +co+ +in+ ? ] map ;


TUPLE: union-type members ;
C: <union-type> union-type
INSTANCE: union-type proper-term
M: union-type from-args* drop <union-type> ;
M: union-type args>> members>> ;
