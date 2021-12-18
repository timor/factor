USING: accessors arrays combinators effects kernel quotations sequences types
types.type-values variants words ;

IN: types.typed-calls

! * Type configuration annotation
! A primitive that allows to erase type information, and also treat some words
! as opaque?

UNION: type-spec effect quotation ;
TUPLE: type-call type-spec quot ;
C: <type-call> type-call
PREDICATE: static-type-call < type-call type-spec>> effect? ;
PREDICATE: dependent-type-call < type-call type-spec>> quotation? ;

GENERIC: >type-call ( object -- type-call )
M: object >type-call
    [ <wrapper> f swap 2array 1array { } swap <effect> ]
    [ literalize 1quotation ] bi <type-call> ;

: word>type-effect ( word -- effect )
    {
        [ stack-effect in>> ]
        [ in-classes ]
        [ stack-effect out>> ]
        [ out-classes ]
    } cleave
    [ [ [ dup pair? [ first ] when ] dip 2array ] 2map ] 2bi@
    <effect> ;
    ! [ stack-effect ]
    ! [ in-classes ]
    ! [ out-classes ] bi <effect> ;
    ! stack-effect effect unboa
    ! [
    !     [ [ dup pair? [ first2 decl>value ]
    !         [ <??> ] if 2array ] map ] bi@
    ! ] 3dip effect boa ;

: static-type-call ( word -- type-call )
    [ word>type-effect ]
    [ 1quotation ] bi <type-call> ;

M: word >type-call
    { { [ dup "shuffle" word-prop ] [ 1quotation dup <type-call> ] }
      [ static-type-call ]
    } cond ;

M: type-call >type-call ;
