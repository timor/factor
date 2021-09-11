USING: accessors arrays assocs combinators.short-circuit effects kernel
sequences sets strings ;

IN: types.unification

! Syntactic first-order unification with row variables
! Note that types here are not factor classes, so some would call these kinds,
! probably

TUPLE: context
    occurs                      ! cache occurrences
    equations ;

: <context> ( -- obj )
    H{ } clone f context boa ;

! * Type expressions

MIXIN: type-expr
INSTANCE: sequence type-expr
! Unfortunately, variants don't support defining identity tuples
TUPLE: type-var < identity-tuple { name string read-only } ;
INSTANCE: type-var type-expr
C: <type-var> type-var

TUPLE: fun-type
    { consumption type-expr read-only }
    { production type-expr read-only } ;
INSTANCE: fun-type type-expr
C: <fun-type> fun-type

TUPLE: row-var < identity-tuple { name string read-only } ;
INSTANCE: row-var type-expr
C: <row-var> row-var

GENERIC: occurs?* ( context var type-expr -- ? )
:: occurs? ( context var expr -- ? )
    var expr context occurs>> [ [ context ] 2dip occurs?* ] 2cache ;

M: sequence occurs?*
    [ occurs? ] with with any? ;

M: type-var occurs?*
    eq? nip ;

M:: fun-type occurs?* ( context var expr -- ? )
    { [ context var expr consumption>> occurs? ]
      [ context var expr production>> occurs? ]
    } 0|| ;

M: row-var occurs?*
    eq? nip ;

! possibly unused?
GENERIC: vars ( type-expr -- seq )
M: sequence vars [ vars ] gather ;
M: type-var vars 1array ;
M: row-var vars 1array ;
M: fun-type vars
    [ consumption>> vars ]
    [ production>> vars ] bi append members ;

GENERIC: element>type-expr ( element -- type-expr )
! TODO: actual types
M: pair element>type-expr
    dup second effect?
    [ second element>type-expr ]
    [ first element>type-expr ] if ;

M: string element>type-expr
    <type-var> ;

: consumption/production>type-expr ( row-var elements -- type-expr )
    [ element>type-expr ] map
    swap prefix ;

: ensure-row-var ( string/f -- string )
    "rho" or ;

: effect-row-vars ( effect -- in-var out-var )
    [ in-var>> ] [ out-var>> ] bi
    [ ensure-row-var ] bi@
    2dup = [ drop <row-var> dup ]
    [ [ <row-var> ] bi@ ] if ;

! Construct type expressions from effects
: effect>type-expr ( effect -- type-expr )
    [ effect-row-vars ]
    [ in>> ] [ out>> ] tri
    swapd [ consumption/production>type-expr ] 2bi@
    <fun-type> ;

M: effect element>type-expr
    effect>type-expr ;

M: configuration element>type-expr
    elements>> [ element>type-expr ] map ;
