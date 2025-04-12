USING: math strings variants ;

IN: terms.unification

! Things to keep in mind:
! - expose bindings in dsl
! - keep access to bindings fast
! - actually have bindings as equiv sets!
! Model: UnifyClosure


<PRIVATE
! Have this in variables for now
! keep track of visited terms
TYPED-VAR: visited hash-set

! prevent cycles
TYPED-VAR: acyclic hash-set

! keep set of vars which belog to the representative
TYPED-VAR: var-set hash-set

! maps representatives from eqs to ground terms
VAR: schema

: unif-closure ( s t -- )
    2dup = [ 2drop ] [

    ] if

PRIVATE>
