USING: accessors classes classes.algebra classes.tuple combinators.short-circuit
effects kernel math.intervals sequences words variants ;

IN: types
! USE: types.transitions.known-words

! * Abstract Domains
MIXIN: domain

! Hacky...
: all-domains ( -- classes )
    domain class-members [ wrapped>> ] map ;


! ** Domain-specific operations
GENERIC: value>type ( value domain -- domain-value )
GENERIC: unknown-type-value ( domain -- domain-value )
GENERIC: apply-class-declaration ( domain-values decl-spec domain -- domain-value )

! This is used to check a state whether it would lead to a divergent calculation
GENERIC: domain-value-diverges?* ( domain-value domain -- ? )
: domain-value-diverges? ( domain-value domain -- ? )
    over ??? [ 2drop f ] [ domain-value-diverges?* ] if ;

! Forward merge of split control paths
GENERIC: type-value-merge ( outn> domain -- >out )
! Undo Forward merge back into split-control path
GENERIC: type-value-undo-merge ( out< out_i< domain -- <out_i )
! Forward split into exclusive control paths
! i - branch index
GENERIC: type-value-perform-split ( in> i domain -- >in )
M: domain type-value-perform-split 2drop ;
! Undo split back into common history of exclusive control-paths
GENERIC: type-value-undo-split ( <out domain -- v< )
! Re-Combination of data-path-split
GENERIC: type-value-undo-dup ( v> <v' domain -- v< )

! Used for returning domain neutral union element
GENERIC: bottom-type-value ( domain -- object )

! Covariant concretization
: and-unknown ( type1 type2 quot: ( type1 type2 -- type ) -- type )
    over ??? [ swapd ] when
    pick ??? [ drop nip ] [ call( x x -- x ) ] if ;

! Covariant concretization
: or-unknown ( type1 type2 quot: ( type1 type2 -- type ) -- type )
    2over [ ??? ] either?
    [ 3drop ?? ] [ call( x x -- x ) ] if ;

! ** Predefined domains
! SINGLETON: value-id
INSTANCE: \ class domain
INSTANCE: \ interval domain
VARIANT: value-id
    +undefined-value+
    scalar: { id }
    branched: { { base value-id } { branch-id } } ;
INSTANCE: \ value-id domain

! * Language of types
GENERIC: type<= ( type1 type2 -- ? )
: type= ( type type -- ? )
    {
        [ type<= ]
        [ swap type<= ]
    } 2&& ;


! This is used to convert literal values into corresponding type-values
GENERIC: type-of ( thing -- base-type )
M: f type-of class-of ;


MIXIN: type
TUPLE: parametric ;
INSTANCE: parametric type
TUPLE: parameter value ;
INSTANCE: parameter type
TUPLE: +inv+ < parameter ; final
TUPLE: +cov+ < parameter ; final
TUPLE: +contrav+ < parameter ; final
: <param> ( value class -- parameter )
    new swap >>value ;
! SINGLETON: +inv+
! SINGLETON: +contrav+
! SINGLETON: +cov+
GENERIC: slot-variance* ( parametric -- seq )
M: parametric slot-variance*
    class-of "slots" word-prop length +inv+ <repetition> ;
: variance ( parametric -- seq )
    superclasses-of [ slot-variance* ] map concat +inv+ prefix ;

TUPLE: literal < parametric class value ;
M: literal slot-variance* drop { +cov+ +cov+ } ;

: >parameter-list ( parametric -- seq )
    parametric check-instance
    [ tuple-slots ] [ variance ] bi
    [ <param> ] 2map ;

M: parametric type<=
    [ >parameter-list ] bi@ type<= ;

! TODO: we cannot compare different variances here, is that correct?
: if-same-kind ( param param quot -- )
    2over class-of = [ [ [ value>> ] bi@ ] dip call ] [ 3drop f ] if ; inline
M: +inv+ type<=
    [ type= ] if-same-kind ;
M: +cov+ type<=
    [ type<= ] if-same-kind ;
M: +contrav+ type<=
    [ swap type<= ] if-same-kind ;

INSTANCE: classoid type
INSTANCE: effect type

M: classoid type<=
    over classoid?
    [ class<= ] [ "undefined comparison" throw ] if ;

! Covariant assumption!
: configuration<= ( ts1 ts2 -- ? )
    2dup shorter? [ 2drop f ] [
        [ type<= ] 2all?
    ] if ;

M: sequence type<= ( types1 types2 -- ? )
    2dup same-length?
    [ [ type<= ] 2all? ]
    [ 2drop f ] if ;

M: effect type<= ( effect1 effect2 -- ? )
    { [ effect<= ]
      [ [ effect-in-types ] bi@ swap configuration<= ]
      [ [ effect-out-types ] bi@ configuration<= ] } 2&& ;


GENERIC: type-or ( type type -- type )

! ! This would be used
! GENERIC: type-and ( type1 type2 -- type )
! M: classoid type-and class-and ;

! : define-atom-predicate ( class -- )
!     object over [ = ] curry define-predicate-class ;

! SYNTAX: ATOM: scan-new-class define-atom-predicate ;

