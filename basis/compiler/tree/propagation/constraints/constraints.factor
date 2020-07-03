! Copyright (C) 2008, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays assocs classes.algebra
compiler.tree.propagation.copy compiler.tree.propagation.info
kernel namespaces sequences ;
IN: compiler.tree.propagation.constraints

SYMBOL: constraints

! assume* seems to be the place where a constraint actually does its work,
! e.g. for a class-constraint, this is where it actually modifies the value
! info.  The constraint was constructed with a specific value.  In assume*, it
! "dereferences" that to the original definer using resolve-copy, creates a
! fresh class-info and uses refine-value-info to update the info for the value
! in the current scope.

! Branches: One of the major uses for constraints is #branch nodes.  Before
! child-tree propagation, this is set based on the condition that the #branch
! dispatches on.  What happens at that point is, that for each branch, exactly
! one constraint is generated for each child-branch, based on the condition
! input to the #branch node.
! TODO(understand) The word `assume` is called on these constraints right before
! propagation is performed.  Why is it not kept lazily?  Let's see:  For #if,
! this should have the effect of immediately setting the value info of the
! condition value to the literal true/false.

! As for `assume`, it is currently invoked:
! - on the condition value before a child branch is taken
! - in a seemingly pretty involved fashion after #phi propagation
! - as part of `follow-implications`, which is invoked when a
!   constant-false-constraint or constant-true-constraint is resolved.  This is
!   pretty cool.  If that constraint has been used to set up implication
!   constraints, basically what happens is that the values is set to the constant
!   t/f, and all other implications based on that constraint are "resolved".  As
!   far as I can tell, purely for the side effects, in effect setting the
!   value-info in the current scope of all dependent values (which must have
!   been established using implication constraints (TODO understand usage of
!   implication constraints)
! - in propagate-before of #call nodes to predicating words, effectively
!   immediately applying the consequences of the predicate
! - in propagate-before of #call nodes which have the "custom-constraints" word
!   property, for which the constraint quotation is evaluated with the input and
!   output values on the stack

! Generally, it looks like `assume` is used eagerly.  (TODO) I haven't
! really understood whether or where a number of "lazy" constraints is first
! built, and then not immediately being "followed through" using `assume`.
! (I think the laziness actually stems from the fact that you define the
! constraint by writing it in the factor compiler scope.  As soon as a value is
! known, the chain is unraveled)

! Btw, a sequence of constraints is treated as a conjunction.  E.g. for #calls
! to predicating words, both the t--> and f--> constraints are established in
! parallel.

GENERIC: assume* ( constraint -- )
GENERIC: satisfied? ( constraint -- ? )

M: f assume* drop ;

M: object satisfied? drop f ;

: assume ( constraint -- ) dup satisfied? [ drop ] [ assume* ] if ;

TUPLE: true-constraint value ;

: =t ( value -- constraint ) resolve-copy true-constraint boa ;

: follow-implications ( constraint -- )
    constraints get assoc-stack [ assume ] when* ;

M: true-constraint assume*
    [ \ f class-not <class-info> swap value>> refine-value-info ]
    [ follow-implications ]
    bi ;

M: true-constraint satisfied?
    value>> value-info*
    [ class>> true-class? ] [ drop f ] if ;

TUPLE: false-constraint value ;

: =f ( value -- constraint ) resolve-copy false-constraint boa ;

M: false-constraint assume*
    [ \ f <class-info> swap value>> refine-value-info ]
    [ follow-implications ]
    bi ;

M: false-constraint satisfied?
    value>> value-info*
    [ class>> false-class? ] [ drop f ] if ;

TUPLE: class-constraint value class ;

: is-instance-of ( value class -- constraint )
    [ resolve-copy ] dip class-constraint boa ;

M: class-constraint assume*
    [ class>> <class-info> ] [ value>> ] bi refine-value-info ;

TUPLE: interval-constraint value interval ;

: is-in-interval ( value interval -- constraint )
    [ resolve-copy ] dip interval-constraint boa ;

M: interval-constraint assume*
    [ interval>> <interval-info> ] [ value>> ] bi refine-value-info ;

TUPLE: literal-constraint value literal ;


! NOTE: This does not establish equivalence between two values.  It asserts that
! a SSA value must be equal to a literal value
: is-equal-to ( value literal -- constraint )
    [ resolve-copy ] dip literal-constraint boa ;

M: literal-constraint assume*
    [ literal>> <literal-info> ] [ value>> ] bi refine-value-info ;

TUPLE: implication p q ;

C: --> implication

: maybe-add ( elt seq -- seq' )
    2dup member? [ nip ] [ swap suffix ] if ;

! I think this is the only location where `constraints` is actually written to...
! Given two BLUBS q and p ( probably constraints, probably of the form p --> q )
! - query the current constraints for the antecedent p, which seems to return a sequence
! - if the consequent is not yet in that sequence, add it to the sequence
! - finally, update the sequence for p in the innermost (i.e. current)
!    constraints scope with that value
: assume-implication ( q p -- )
    [ constraints get [ assoc-stack maybe-add ] 2keep last set-at ]
    [ satisfied? [ assume ] [ drop ] if ] 2bi ;

M: implication assume*
    [ q>> ] [ p>> ] bi assume-implication ;

TUPLE: equivalence p q ;

C: <--> equivalence

M: equivalence assume*
    [ p>> ] [ q>> ] bi
    [ assume-implication ]
    [ swap assume-implication ] 2bi ;

! Conjunction constraints -- sequences act as conjunctions
M: sequence assume* [ assume ] each ;

! I think this means: Establish the notion that if BOOLEAN-VALUE is t,
! CONSTRAINT holds.
: t--> ( constraint boolean-value -- constraint' ) =t swap --> ;

! Likewise, this would mean that if BOOLEAN-VALUE is f, CONSTRAINT holds
: f--> ( constraint boolean-value -- constraint' ) =f swap --> ;
