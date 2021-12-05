USING: accessors classes kernel types.parametric types ;

IN: types.parametric.literal

! ! * Instance Type
! ! Meta-Object
! ! Used to indicate that a value is an instance of a class.
! ! Used on typestacks, basically only a wrapper that represents a value that can
! ! take up the entire value range
! TUPLE: instance-type < anonymous-predicate ;
! : <instance-type> ( class -- type )
!     [ superclass>> instance? ] instance-type boa ;

! * Parametric Equality test class

! Has the effect of creating a singleton type for a value, which is defined as a
! parametric anonymous predicate class on the value's class.

! These are not defined on a fixed class, but the class of whatever is
! literalized.
! Intersection test is equality check, test is =
TUPLE: literal-type < anonymous-predicate value ;

: <class/literal-type> ( superclass value -- type )
    [ value>> = ] swap literal-type boa ;

! Defined on values!
: <literal-type> ( value -- type )
    [ class-of ] keep <class/literal-type> ;

! This one is like a tag, it cannot be optimized away by an intersection with
! any builtin class.
! TUPLE: eql-type < literal-type ;
: <eql> ( value -- type )
    object swap <class/literal-type> ;
    ! [ object [ value>> = ] ] dip eql-type boa ;

! TUPLE: eql-type < literal-type ;
! : <eql> ( value -- type )
!     ! object swap <class/literal-type> ;
!     [ object [ value>> = ] ] dip eql-type boa ;

! M: eq-type parameter-classes-intersect?
!     2drop t ;

M: literal-type parameter-classes-intersect?
    over literal-type?
    [ [ value>> ] bi@ = ]
    ! Worst case assumption:
    [ 2drop t ] if ;

! Recover the literal from the type, or return the value itself
: literal>value ( type class -- value ? )
    { { [ 2dup instance? ] [ drop t ] }
      { [ over literal-type? ] [ 2dup class<= [ drop value>> t ] [ drop f ] if ] }
      [ drop f ]
    } cond ;

M: object type-of <literal-type> ;
