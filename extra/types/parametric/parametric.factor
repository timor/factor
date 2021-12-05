USING: accessors classes classes.algebra classes.algebra.private classes.private
effects kernel quotations sequences types ;

IN: types.parametric

! * Parametric Predicate types
! These are characterized by providing access to the parameters they have been defined with.

TUPLE: anonymous-predicate
    { superclass maybe{ type } read-only }
    { definition maybe{ callable } read-only } ;
INSTANCE: anonymous-predicate classoid
M: anonymous-predicate superclass-of superclass>> ;
! These definitions are copied from the predicate class implementations
M: anonymous-predicate rank-class drop 2 ;
! These definitions are distinct from the predicate class implementations

! This is the default implementation.  Subclasses implement their parameter-specific behavior here
! NOTE: in order for these classes to intersect, their superclasses have to intersect
GENERIC: parameter-classes-intersect? ( class1 class2 -- ? )
! worst case assumptions, if superclasses intersect, this is called, so we
! assume restrictions are too lax unless specified otherwise by subtype implementations
M: classoid parameter-classes-intersect?
    2drop t ;

! NOTE: since we installed ourselves with class rank 2, we also have to handle
! lower ranked classes as first argument.  Only in the case where we actually
! have to deal with another parametric class can the verdict by the superclass
! test be negated
M: anonymous-predicate (classes-intersect?)
    2dup superclass-of classes-intersect?
    [ over anonymous-predicate?
      [ parameter-classes-intersect? ] [ 2drop t ] if ]
    [ 2drop f ] if ;

M: anonymous-predicate instance?
    2dup superclass-of instance? [
        dup definition>> call( parameter-class object -- ? )
    ] [ 2drop f ] if ;

M: anonymous-predicate class-name
    superclass-of class-name "‡" append ;

M: anonymous-predicate effect>string
    class-name ;
