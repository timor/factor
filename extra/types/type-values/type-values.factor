USING: accessors arrays assocs assocs.extras classes classes.algebra
classes.private columns combinators.short-circuit continuations delegate
delegate.protocols formatting grouping hashtables kernel math math.functions
math.intervals math.parser prettyprint.backend prettyprint.custom sequences
sequences.zipped sets types types.util variants ;

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

: map-domains ( quot: ( ..a key -- ..b elt ) -- assoc )
    all-domains [ swap keep swap ] with
    H{ } map>assoc ; inline

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
    [ over ??? [ drop word-name* ] [ pprint-domain-value* ] if ] if ;

: pprint-type-value ( type-value -- )
    dup ! map>>
    all-domains [ [ of ] keep pprint-domain-value ] with map
    "|" join "V(" ")" pprint-string ;

M: type-value pprint* pprint-type-value ;

! FUBAR with the prettyprinting protocol here, I simply don't understand it....
M: \ class pprint-domain-value* drop
    dup wrapper? [ class-name ]
    [ word-name* ] if ;
GENERIC: >bound-string ( number -- str )
M: number >bound-string
    abs 2 logn "2^%.1f" sprintf ;
M: fixnum >bound-string
    dup abs 1024 <= [ number>string ] [ call-next-method ] if ;

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
: map-value-domains ( type-value quot: ( domain-value domain -- domain-value ) -- type-value )
    ! [ map>> ] dip
    '[ swap _ keep swap members
    ] assoc-map type-value boa
    ! simplify-type-value
    ; inline

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
: with-domain-stacks ( values quot-assoc -- values )
    [ unzip-domains ] dip
    [ with-datastack ] assoc-merge
    zip-domains ;
