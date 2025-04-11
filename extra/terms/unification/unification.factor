USING: math strings variants ;

IN: terms.unification

! Things to keep in mind:
! - expose bindings in dsl
! - keep access to bindings fast
! - actually have bindings as equiv sets!
! Model: UnifyClosure


! keep track of visited terms
VAR: visited

! prevent cycles
VAR: acyclic

! keep set of vars which belog to the representative
VAR: var-set

! maps representatives from eqs to ground terms
VAR: schema

: unif-closure ( s t -- )
    2dup eqs representatives
    2dup eq? [ 2drop ] [
        j
    ] if
