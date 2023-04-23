USING: accessors arrays chr.factor classes.tuple combinators.smart hash-sets
kernel sequences terms ;

IN: chr.factor.util

! ! GENERIC: same-effect? ( t1 t2 -- ? )
! ! :: same-xor? ( x1 x2 -- ? )
! !     x1 type1>> x2 type1>> same-effect?
! !     x1 type2>> x2 type2>> same-effect? and ;

! ! M: Xor same-effect?
! !     over Xor?
! !     [ { [ same-xor? ]
! !         [ [ type2>> ] [ type1>> ] bi Xor boa same-xor? ] } 2||
! !     ] [ 2drop f ] if ;

! GENERIC: pred<=> ( o1 o2 -- <=> )
! M: chr-pred pred<=>
!     over chr-pred?
!     [ [ tuple>array ] bi@ pred<=> ]
!     [ call-next-method ] if ;
! M: word pred<=> <=> ;
! M: term-var pred<=>
!     over term-var?
!     [ 2drop +eq+ ]
!     [ call-next-method ] if ;
! M: object pred<=> [ class-of ] compare ;
! M: sequence pred<=>
!     [ mismatch ] 2keep pick [ 2nth-unsafe pred<=> ] [ [ length ] compare nip ] if ;
! M: list pred<=>
!     [ llength* ] compare ;

! : same-set? ( s1 s2 -- <=> )
!     { [ [ cardinality ] same? ]
!       [ [ [ pred<=> ] sort ] bi@
!         [ same-effect? ] 2all? ]
!     } 2&& ;
GENERIC: expand-xor ( xor -- seq )
M: Xor expand-xor [ type1>> ] [ type2>> ] bi
    [ expand-xor ] bi@ append ;
M: object expand-xor 1array ;

GENERIC: effect>nterm ( effect -- term )
M: Xor effect>nterm
    expand-xor
    [ effect>nterm ] map >hash-set ;

M: object effect>nterm ;

M: Instance effect>nterm
    clone [ effect>nterm ] change-type ;

M: Effect effect>nterm
    {
        [ in>> ]
        [ out>> ]
        [ preds>>
          [ effect>nterm ] map >hash-set
        ]
        [ parms>> >hash-set ]
    } cleave>array ;

: same-effect? ( e1 e2 -- ? )
    [ effect>nterm ] bi@ isomorphic? ;

! TODO: effect predicates set comparison (expensive!)
