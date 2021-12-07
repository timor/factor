USING: accessors arrays classes.algebra classes.algebra.private combinators
combinators.short-circuit compiler.utilities effects kernel quotations sequences
stack-checker types types.parametric types.protocols ;

IN: types.parametric.effects


! * Effect types and typed quotations
TUPLE: effect-type < anonymous-predicate
    effect ;
M: effect-type type>classoid ;

: check-quotation ( quotation quotation-type -- ? )
    ! [ infer-effect ] dip effect<= ;
    [ infer ] [ effect>> ] bi* effect<= ;

: normalize-effect ( effect -- effect )
    {
        [ in-var>> ]
        [ out-var>> ]
        [ effect-in-types ]
        [ effect-out-types ]
    } cleave
    [ [ f swap 2array ] map ] bi@
    swapd
    <variable-effect> ;

: <typed-quotation> ( effect -- type )
    [ callable [ check-quotation ] ] dip
    normalize-effect
    effect-type boa ;

! M: effect type-of <typed-quotation> ;
M: effect type-of ;
M: effect type>classoid <typed-quotation> ;

PREDICATE: empty-quotation < quotation empty? ;
CONSTANT: empty-quotation-type T{ effect-type f callable [ drop empty-quotation? ] ( -- ) }
M: empty-quotation type-of drop empty-quotation-type ;
! M: quotation type-of
!     [ infer-effect type-of ] keep <class/literal-type> ;

! * TODO Subtype relations on quotation types

! Covariant arrow type: inputs are contravariant, while outputs are covariant.
! NOTE: for now, only checking input configuration, since we assume forward
! substitutability only.
! Row effects are virtual infinite sequences with object per default.
! The longer it is, the more specific it is
! Assuming same configuration of fixed-elements:
! bivariable-effect is more general than variable-effect if considering the output

! Conditions for being a subtype on the input configuration:
! - all inputs must be supertypes
! - → all defined inputs must be supertypes
! - undefined inputs means it must work on empty stack → if effect is known to
! be longer, it can not be a subtype

M: effect-type custom-class-order? drop t ;
: elements<= ( effect1 effect2 -- ? )
    [ class<= ] 2all? ;

: row<= ( types1 types2 -- ? )
    longer? not ;

: if-effect-type ( first second quot -- )
    pick effect-type? [ call ] [ 3drop f ] if ; inline

! Contravariant
: consumption<= ( types types -- ? )
    { [ row<= ] [ [ <reversed> ] bi@ swap elements<=  ] } 2&& ;

! Covariant
! For the outputs, we pad with objects, since a smaller effect height is admissible
: production<= ( types types -- ? )
    object pad-head-shorter elements<= ;

M: effect-type custom-class<= ( first second -- ? )
    [
        [ effect>> ] bi@
        {
            [ [ bivariable-effect? ] either? not ]
            [ [ effect-height ] same? ]
            [ [ effect-in-types ] bi@ consumption<= ]
            [ [ effect-out-types ] bi@ production<= ]
        } 2&&
    ] if-effect-type ;

! Union of two quotation types on the type stack.
! A quotation with a bivariable effect can be considered higher-order.  These
! are basically incomparable, so all we know is that we need a quotation
