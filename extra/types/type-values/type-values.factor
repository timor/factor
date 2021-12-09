USING: accessors arrays assocs assocs.extras classes classes.algebra
classes.private columns combinators.short-circuit continuations delegate
delegate.protocols formatting grouping hashtables kernel math math.functions
math.intervals math.parser prettyprint.backend prettyprint.custom sequences
sequences.zipped sets types types.util ;

IN: types.type-values

! * Intersection top level type
TUPLE: type-value map ;
M: type-value clone
    call-next-method
    [ clone ] change-map ;

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

! ** Disjoint union of type values
TUPLE: disjoint-union values ;

GENERIC: pprint-domain-value* ( type-value domain -- str )
: pprint-domain-value ( type-value domain -- str )
    over sequence?
    [ [ pprint-domain-value ] curry map " " join "{" "}" surround ]
    [ over ??? [ drop class-name ] [ pprint-domain-value* ] if ] if ;

: pprint-type-value ( type-value -- )
    dup ! map>>
    all-domains [ [ of ] keep pprint-domain-value ] with map
    "|" join "V(" ")" pprint-string ;

M: type-value pprint* pprint-type-value ;

M: \ class pprint-domain-value* drop class-name ;
GENERIC: >bound-string ( number -- str )
M: number >bound-string
    abs 2 logn "2^%.1f" sprintf ;
M: fixnum >bound-string
    dup 1024 <= [ number>string ] [ call-next-method ] if ;

: interval-bound>string ( number -- str )
    [ 0 < "-" "" ? ]
    [ >bound-string ] bi append ;

M: \ interval pprint-domain-value* drop
    [ from>> first2 swap
      [ "[" "(" ? ] [ interval-bound>string ] bi*
      append "," append ]
    [ to>> first2
      [ interval-bound>string ] [ "]" ")" ? ] bi*
      append append
     ] bi ;
M: \ value-id pprint-domain-value* drop
    "#%d" sprintf ;

! Destructive
: normalize-type-value ( type-value -- type-value )
    [ [ dup sequence? [ 1array ] unless ] assoc-map ] change-map ;

! Destructive
: simplify-type-value ( type-value -- type-value )
    [ [ dup { [ sequence? ] [ length 1 = ] } 1&& [ first ] when ] assoc-map ] change-map ;

! Copies
: map-domains ( type-value quot: ( domain-value domain -- domain-value ) -- type-value )
    ! [ map>> ] dip
    '[ swap _ keep swap members
    ] assoc-map type-value boa
    ! simplify-type-value
    ; inline

! Assumes that all domain value sets specify disjoint unions of domain values
: apply-declaration ( type-value decl -- type-value )
    ! [ normalize-type-value ] dip
    [ apply-domain-declaration ] with map-domains ;

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

! Parallel merge, forward
: squish-type-values ( type-values -- type-value )
    unzip-domains
    [ [ swap type-value-merge ] keep swap ] assoc-map <type-value> ;

! Undo parallel merge, backward.
! We have kept the list of branch values, and now intersect the merged state
! against the memorized pre-merge branch states.
: unsquish-type-values ( type-values type-value -- type-value )
    [ unzip-domains ] dip
    '[ [ _ rot type-value-undo-merge ] keep swap ] assoc-map <type-value> ;

! Stack of type infos.  Split according to domains.  Elements are members of the domain.
: with-domain-stacks ( values quot-assoc -- values )
    [ unzip-domains ] dip
    [ with-datastack ] assoc-merge
    zip-domains ;
