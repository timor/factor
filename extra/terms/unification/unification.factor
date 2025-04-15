USING: choose-fail classes classes.tuple combinators combinators.short-circuit
hash-sets hashtables kernel sequences sets terms terms.context variables ;

IN: terms.unification

! Things to keep in mind:
! - expose bindings in dsl
! - keep access to bindings fast
! - actually have bindings as equiv sets!
! - don't actually run subst until it is known that schema is needed?
! Model: UnifyClosure

GENERIC: unify-terms ( term1 term2 -- )

<PRIVATE
! Have this in variables for now
! keep track of visited terms
TYPED-VAR: visited hash-set

! prevent cycles
TYPED-VAR: acyclic hash-set

! keep set of vars which belog to the representative
TYPED-VAR: var-set hashtable

! maps representatives from eqs to ground terms
! TODO: this must probably be escalated to global level to keep around after
! unification efficiently?
! TYPED-VAR: schema persistent-hash

: vars-union ( s t -- )
    2dup equate-vars
    dup var-rep var-set '[ _ _ adjoin-at ] bi@ ;

: unif-closure ( s t -- )
    [ get-schema ] bi@ 2dup = [ 2drop ]
    [
        ! 2dup [ term-var? ] both?
        ! [ [ get-schema ] bi@ ] when
        2dup [ term-var? ] bi@
        { { [ 2dup and ] [ 2drop vars-union ] }
          { [ 2dup or not ] [ 2drop unify-terms ] }
          { [ dup ] [ 2drop set-rep-schema ] }
          [ 2drop swap set-rep-schema ]
        } cond
    ] if ;

PRIVATE>

: unify-sequence ( seq1 seq2 -- )
    [ unif-closure ] 2each ;

M: sequence unify-terms
    2dup { [ drop sequence? ]
           [ [ length ] same? ]
    } 2&&
    [ unify-sequence ]
    [ fail ] if ;

M: tuple unify-terms
    2dup [ class-of ] same?
    [ [ tuple-slots ] bi@ unify-sequence ]
    [ fail ] if ;

M: term-var unify-terms
    "nope" throw ;

M: object unify-terms
    = [ fail ] unless ;

! compute only unifier
: unifier ( s t -- term-relation vars )
    [ unif-closure equivs var-set ] choosing with-equiv-scope ;

! term building
! : find-solution
