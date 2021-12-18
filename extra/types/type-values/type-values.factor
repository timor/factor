USING: accessors arrays assocs assocs.extras classes classes.algebra
classes.private columns combinators.short-circuit compiler.tree.propagation.info
continuations delegate delegate.protocols effects formatting generic.math
grouping hash-sets hashtables kernel math math.functions math.intervals
math.parser namespaces prettyprint.backend prettyprint.custom sequences
sequences.zipped sets typed types types.util variants words ;

IN: types.type-values


! * Intersection top level type
TUPLE: type-value map ;
M: type-value clone
    call-next-method
    [ clone ] change-map ;

! expensive checking
PREDICATE: type-stack < sequence [ type-value? ] all? ;

CONSULT: assoc-protocol type-value
    map>> ;

: <type-value> ( assoc -- obj )
    >hashtable dup keys [ domain? ] all?
    [ type-value boa ] [ "invalid-domain-assoc" throw ] if ;

: <??> ( -- type-value )
    all-domains [ dup unknown-type-value ] H{ } map>assoc
    type-value boa ;

: >value ( obj -- type-value )
    all-domains [ tuck value>type ] with H{ } map>assoc
    type-value boa ;

: decl>value ( class-decl -- type-value )
    [ swap class>domain-value ] curry map-domains
    type-value boa ;

! Returns pairs { declarations type-values }
: effect>class/type-values ( effect -- in-values out-values )
    [ in>> ] [ out>> ] bi
    [ [ dup pair? [ second ] [ drop ?? ] if dup decl>value 2array ] map ] bi@ ;

! ** Disjoint union of type values
TUPLE: disjoint-union values ;

GENERIC: pprint-domain-value* ( type-value domain -- str )
M: object pprint-domain-value* nip class-name ;
: pprint-domain-value ( type-value domain -- str )
    over sequence?
    [ [ pprint-domain-value ] curry map " " join "{" "}" surround ]
    [ over ??? [ drop word-name* ] [ pprint-domain-value* ] if ] if ;

: pprint-type-value ( type-value -- )
    dup ! map>>
    all-domains [ [ of ] keep pprint-domain-value ] with map
    "|" join "V(" ")" pprint-string ;

M: type-value pprint* pprint-type-value ;
! TODO fix FUBAR and correctly switch to pprint implementation...
M: \ effect pprint-domain-value* drop effect>string ;

! TODO
! FUBAR with the prettyprinting protocol here, I simply don't understand it....
M: \ class pprint-domain-value* drop
    dup word? [ word-name* ]
    [ class-name ] if ;
    ! dup wrapper? [ class-name ]
    ! [ word-name* ] if ;
GENERIC: >bound-string ( number -- str )
M: number >bound-string
    2 logn "2^%.1f" sprintf ;
M: fixnum >bound-string
    dup 1024 <= [ number>string ] [ call-next-method ] if ;
M: \= 1/0. >bound-string drop "∞" ;

: interval-bound>string ( number -- str )
    [ 0 < "-" "" ? ]
    [ abs >bound-string ] bi append
    ;

M: \ interval pprint-domain-value* drop
    [ from>> first2 swap
      [ "[" "(" ? ] [ interval-bound>string ] bi*
      append "," append ]
    [ to>> first2
      [ interval-bound>string ] [ "]" ")" ? ] bi*
      append append
     ] bi ;

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
M: \ interval class>domain-value drop
    class-invariant>interval ;


: value-id>str ( value-id -- str )
    dup ??? [ word-name* ]
    [ {
       { +undefined-value+ [ "?VAL" ] }
       { scalar [ number>string ] }
       { branched [ [ value-id>str ] [ number>string ] bi* "." glue ] }
    } match ] if ;

M: \ value-id pprint-domain-value* drop
    ! "%u" sprintf ;
    members [ value-id>str "#%s" sprintf ] map " " join "{" "}" surround ;

! Destructive
: normalize-type-value ( type-value -- type-value )
    [ [ dup sequence? [ 1array ] unless ] assoc-map ] change-map ;

! Destructive
: simplify-type-value ( type-value -- type-value )
    [ [ dup { [ sequence? ] [ length 1 = ] } 1&& [ first ] when ] assoc-map ] change-map ;

! Copies
:: map-value-domains ( type-val quot: ( domain-value domain -- domain-value ) -- type-value )
    type-val [| dom dom-val | dom-val dom quot call( x x -- x ) dom swap ] assoc-map
    type-value boa ;

: divergent-type-value? ( type-value -- ? )
    [ dup sequence? [ 1array ] unless swap [ domain-value-diverges? ] curry any? ] assoc-any? ;

: unzip-domains ( type-values -- assoc )
    all-domains [ [ [ of ] curry <mapped> ] keep swap ] with
    H{ } map>assoc ;

: zip-domains ( assoc -- type-values )
    dup values [ length ] <mapped> all-equal?
    [ "unbalanced parallel domain value stacks" 2array throw ] unless
    unzip [ 1array ] dip <flipped>
    [ <zipped> ] cartesian-map first [ <type-value> ] map ;

: divergent-stack? ( type-values -- ? )
    [ [ swap domain-value-diverges? ] assoc-any? ] any? ;


! This applies user-supplied declarations which always contain classes
: apply-declaration ( type-values decl -- type-values )
    [ unzip-domains ] dip
    [ pick apply-class-declaration ] curry assoc-map
    zip-domains ;
    ! [ normalize-type-value ] dip
    ! [ apply-class-declaration ] with map-value-domains ;

! Parallel merge, forward
: squish-type-values ( type-values -- type-value )
    unzip-domains
    [ over type-value-merge ] assoc-map <type-value> ;

! Undo parallel merge, backward.
! We have kept the list of branch values, and now intersect the merged state
! against the memorized pre-merge branch states.
: unsquish-type-values ( type-values type-value -- type-value )
    [ unzip-domains ] dip
    '[ [ _ rot type-value-undo-merge ] keep swap ] assoc-map <type-value> ;

! Stack of type infos.  Split according to domains.  Elements are members of the domain.
! Applies each domain quotation to the domain stack, returns the combined type-values
: with-domain-stack ( domain-values quot -- domain-values )
    with-datastack ;

TYPED: with-domain-stacks ( values: type-stack quot-assoc -- values: type-stack )
    [ unzip-domains ] dip
    [ with-domain-stack ] assoc-merge
    zip-domains ;

: domain-intersects? ( value value domain -- ? )
    [ domain-intersect ]
    [ domain-value-diverges? not ] bi ;

: stacks-intersect? ( values values -- ? )
    [ unzip-domains ] bi@
    [| dom a1 a2 |
     a1 dom of
     a2 dom of
     [ dom domain-intersects? ] 2all?
    ] 2curry all-domains swap all? ;

: intersect-type-values ( value1 value2 -- value )
    2dup = [ drop ]
    [
        [| dom a1 a2 |
         a1 dom of
         a2 dom of
         dom domain-intersect
        ] 2curry map-domains
    ] if ;

: intersect-type-stack ( stack values -- stack )
    [
        intersect-type-values
    ] 2map-suffix ;

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
M: \ value-id class>domain-declaration drop length ?? <repetition> ;
M: \ value-id apply-domain-declaration 2drop ;
M: \ value-id class>domain-value nip unknown-type-value ;
! M: \ value-id domain-intersects? drop intersects? ;
M: \ value-id domain-intersect drop intersect ;

! * Class algebra
M: \ class type-value-merge drop [ ] [ class-or ] map-reduce ;
M: \ class type-value-undo-merge drop class-and ;
M: \ class type-value-undo-dup drop [ class-and ] and-unknown ;
M: \ class value>type drop <wrapper> ;
! M: \ class unknown-type-value drop object ;
M: \ class unknown-type-value drop ?? ;
M: \ class domain-intersect drop class-and ;

! NOTE: Concretization necessary here?
M: \ class apply-class-declaration drop
    [ [ class-and ] and-unknown ] 2map-suffix ;
M: \ class domain-value-diverges?* drop null = ;
M: \ class bottom-type-value drop null ;
M: \ class type-value-undo-split type-value-merge ;
M: \ class class>domain-declaration drop ;
M: \ class apply-domain-declaration drop
    [ class-and ] and-unknown ;
! TODO: any concretization necessary?
M: \ class class>domain-value drop ;

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
! M: \ interval unknown-type-value drop full-interval ;
M: \ interval unknown-type-value drop ?? ;
M: \ interval domain-intersect drop [ interval-intersect ] and-unknown ;
