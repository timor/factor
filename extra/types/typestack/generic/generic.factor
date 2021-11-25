USING: classes combinators combinators.short-circuit effects kernel math
quotations sequences types types.typestack vectors words ;

IN: types.typestack.generic

! * Generic dispatch for type-level computations

! Calculates which dispatch is more specific.  This is used to order
! signatures.  This is different from regular type<= relation in that for
! two effects, the subtype relation depends on the outputs in a covariant
! manner.

! TODO: on the other hand, we might be able to enforce a strict order here in
! terms of subtyping if an automatic inverse should be deterministic?

GENERIC: dispatch<= ( type1 type2 -- ? )
M: effect dispatch<=
    [ effect check-instance ] dip
    [ effect-in-types ] bi@ configuration<= ;

ERROR: incomparable-dispatch type1 type2 ;

: dispatch< ( effect effect -- ? )
    { { [ 2dup dispatch<= not ] [ 2drop f ] }
      { [ 2dup swap dispatch<= not ] [ 2drop t ] }
      [ 2drop f ]
    } cond ;

: effect-can-dispatch? ( typestack effect -- ? )
    effect-in-types configuration<= ;

PREDICATE: type-macro < word "type-methods" word-prop >boolean ;

: type-methods ( word -- seq )
    "type-methods" word-prop ;

PREDICATE: type-dispatch-spec < sequence
    { [ length 3 = ] [ first effect? ] [ second callable? ] [ third callable? ] } 1&& ;

: spec-dispatch-effect ( spec -- effect ) first ;

ERROR: dispatch-sort-failed ;
! Covariant ordering, implementation copied from class algebra
! : largest-dispatch-type ( seq -- n elt )
!     dup [ [ dispatch< ] with none? ] curry find-last
!     [ dispatch-sort-failed ] unless* ;
! NOTE: classes are tested for class<.  So the class list is searched for an
! entry that is not strictly smaller than any other.  This means it must be
! larger or equal than all others.
! However we need to ensure that none are equal to find the largest.  So the
! largest is one that is not smaller or equal to any other.  We cannot use the
! original test, since that would correctly skip itself in the search list, but
! we need to be able to distinguish between ourselves and another possibly equal
! dispatch spec.

! If the element at position i is the largest dispatch spec,
! it can not be smaller or equal than any other.  So we search for any other
! that is smaller or equal.
! If we found one, we know
! that this is not the largest one.
:: largest-dispatch-spec? ( seq i -- ? )
    seq i seq nth :> test
    [| elt j |
     j i = [ f ]
     [ test elt [ spec-dispatch-effect ] bi@ dispatch<= ] if
    ] find-index nip not ;

: largest-dispatch-spec ( seq -- n elt )
    [ dup length [ largest-dispatch-spec? ] with find-integer ]
    keep over
    [ dupd nth ]
    [ dispatch-sort-failed ] if ;

    ! dup [ [ [ spec-dispatch-effect ] bi@ dispatch<= ] with none? ] curry find-last
    ! [ dispatch-sort-failed ] unless* ;

! : largest-dispatch-spec ( seq -- n elt )
!     [ spec-dispatch-effect ] map largest-dispatch-type ;

: sort-dispatch-specs ( specs -- specs )
    >vector
    [ dup empty? not ] [ dup largest-dispatch-spec [ swap remove-nth! ] dip ]
    produce nip ;

! NOTE: the input effect types of the word itself have already been applied to
! the type stack when this is called.
M: type-macro type-transfer*
    type-methods [ effect-can-dispatch? ] with filter
    sort-dispatch-specs last
    [ second ] [ third ] bi ;
