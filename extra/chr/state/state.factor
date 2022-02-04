USING: accessors arrays assocs assocs.extras chr chr.parser combinators
combinators.short-circuit disjoint-sets hash-sets kernel linked-assocs math
namespaces quotations sequences sets typed types.util words ;

IN: chr.state

TUPLE: chr-state stack store builtins trace n vars ;

FROM: namespaces => set ;

SYMBOLS: program exec-stack store builtins match-trace current-index ;

: reset-chr-state ( -- )
    exec-stack off
    store off
    builtins off
    match-trace off
    0 current-index set ;

: with-new-chr-state ( quot -- )
    [ reset-chr-state ] prepose with-scope ; inline

: get-chr-state ( -- assoc )
    { program exec-stack store builtins match-trace current-index }
    [ dup get ] H{ } map>assoc ;


! Operational interface
TUPLE: chr-suspension
    constraint id alive activated stored hist vars ;

SLOT: type
SLOT: args
M: chr-suspension type>> constraint>> constraint-type ;
M: chr-suspension args>> constraint>> constraint-args ;

! This is an interface var, which can change during rule processing
SYMBOL: substitutions
SINGLETON: rule-fail

: local-var? ( variable -- ? )
    [ program get local-vars>> in? ] [ f ] if* ;

DEFER: activate-new
! Interface for builtin solvers!
: maybe-add-atom ( x ds -- )
    2dup disjoint-set-member?
    [ 2drop ] [ add-atom ] if ; inline
: assume-equal ( a b ds -- )
    {
        [ nipd maybe-add-atom ]
        [ nip maybe-add-atom ]
        [ equate ]
    }
    3cleave ;

DEFER: reactivate
:: wake-equal ( v k -- )
    store get [| id sus |
               sus vars>> :> vs
               { [ v vs in? ] [ k vs in? ] } 0||
               [ id reactivate ] when
    ] assoc-each ;

DEFER: test-eq
: add-equal ( value key -- new )
    2dup [ local-var? ] either?
    [ "equating locals!" throw ] when
    2dup test-eq
    [ 2drop f ]
    [ [ defined-equalities get assume-equal ]
      [ 2array \ = prefix 1array ]
      [ wake-equal ]
      2tri ] if ;

    ! substitutions get set-at ; inline

TYPED: create-chr ( c: chr-constraint -- id )
    chr-suspension new swap
    [ >>constraint ]
    [ vars >hash-set >>vars ] bi
    t >>alive
    current-index [ 0 or 1 + dup ] change [ >>id ] keep
    [ store get set-at ] keep ;

: alive? ( id -- ? )
    store get at [ alive>> ] [ f ] if* ;

DEFER: activate
: reactivate ( id -- )
    dup alive? [ activate ] [ drop ] if ;
    ! store get at t >>activated drop ;

! : reactivate-all ( -- )
!     store get [ constraint>> constraint-fixed? [ drop ] [ reactivate ] if ] assoc-each ;

:: kill-chr ( id -- )
    store get dup id of
    [ f >>alive drop id
      ! 2drop
      swap delete-at
    ]
    [ drop ] if* ;
! * Matching
! Matching: Todo-list of things to try


! A constraint has been activated, and for each occurrence this is executed:
! Fetch the rule this occurrence is in, construct a list of heads to check (which
! excludes this one)
! 1. If there is one
!    - Try to match against all activated constraints in the store
!      - Perform a match using the current substitution, add that to the current
!        subst
!        - Exclude Candidate in Store if at least one of the following applies:
!          - The constraint type differs
!          - The constraint is dead
!          - We already matched against it
!    - If the match fails, return failure
!    - If the match succeeds, repeat 1. with the rest of the occurrrences, note
!      down id of matched constraint
! 2. If the list is empty, and match succeeded
!   - Check the guards
!   - Kill all applicable constraints
!   - Add history info
!   - execute body

: lookup ( ctype -- seq )
    store get [ type>> = ] with filter-values ;

:: check/update-history ( rule-id trace -- ? )
    trace keys :> matched
    matched rule-id prefix :> sig
    matched store get extract-keys values sift :> stored-cs
    sig stored-cs [ hist>> in? ] with all?
    [ f ]
    [ stored-cs [ [ sig suffix ] change-hist drop ] each t ] if ;

: check-guards ( rule-id bindings -- ? )
    [ program get rules>> nth ] dip
    swap guard>> [ test-constraint ] with all? ;

: apply-substitution ( subst constraint -- constraint )
    apply-substitution* ;

! TODO: Don't use t as special true value in body anymore...
: run-rule-body ( rule-id bindings -- )
    [ program get rules>> nth ] dip
    swap body>> dup t =
    [ 2drop ] [ [ apply-substitution activate-new ] with each ] if ;

: simplify-constraints ( trace -- )
    [ [ drop ] [ kill-chr ] if ] assoc-each ;

: fire-rule ( rule-id trace bindings -- )
    { [ nip check-guards ]
      [ drop check/update-history ]
      [ drop nip simplify-constraints t ]
      [ nip run-rule-body t ]
    } 3&& drop ;

: start-match ( var-term arg-term -- subst )
    2array 1array H{ } clone swap solve-next ;

: match-constraint ( bindings args constraint -- bindings )
    constraint-args swap 2array 1array solve-next ; inline

! Every level is passed the following info:
! rule-id { { id0 keep0 } ...{ id1 keep1} } bindings
:: (run-occurrence) ( rule-id trace bindings partners -- )
    partners empty? [
        trace [ drop alive? ] assoc-all?
        [ rule-id trace bindings fire-rule ] when
    ] [
        partners unclip-slice :> ( rest next )
        next first2 :> ( keep-partner pc )
        pc constraint-type lookup
        [| sid sc |
         { [ sid trace key? not ] [ sc alive>> ] } 0&& [
             bindings sc args>> pc match-constraint :> bindings1
             bindings1 [
                 rule-id trace sid keep-partner 2array suffix bindings1 rest (run-occurrence)
             ] when
         ] when
        ] assoc-each
    ] if ;


:: run-occurrence ( c schedule --  )
    c id>> :> active-id
    schedule [ occurrence>> first ] [ arg-vars>> ] [ partners>> ] tri
    :> ( rule-id arg-vars partners )
    rule-id active-id schedule keep-active?>> 2array 1array
    arg-vars c args>> start-match
    [ partners (run-occurrence) ] [ 2drop ] if* ;

SYMBOL: sentinel

: recursion-check ( -- )
    sentinel get 500 > [ "runaway" throw ] when
    sentinel inc ;

! TODO: check if that is needed to make sure tail recursion works!
! Don't reactivate ourselves, don't reactivate more than once!
: activate ( id -- )
    store get at
    dup activated>>
    [ drop ]
    [
        dup t >>activated
        recursion-check
        dup type>> program get schedule>> at
        [ run-occurrence ] with each
        f >>activated drop
    ] if ;

GENERIC: activate-new ( c -- )
M: sequence activate-new
    [ activate-new ] each ;

M: chr-constraint activate-new
    recursion-check
    create-chr activate ;

M: generator activate-new
    [ body>> ]
    [ vars>> [ dup dup word? [ name>> ] when uvar <gvar>
             ] H{ } map>assoc ] bi lift
    activate-new ;

M: true activate-new drop ;

! Interface for builtin solving
! NOTE: This tests alpha-equality
: test-eq ( lhs rhs -- ? )
    solve-eq { [  ] [ assoc-empty? ] } 1&& ;

M: callable activate-new
    recursion-check
    call( -- new )
    ! reactivate-all
    activate-new ;

! TODO: check whether in-place store modification is sound
M: chr-suspension apply-substitution*
    [ apply-substitution* ] change-constraint ;

: with-chr-prog ( prog quot -- )
    [ LH{ } clone store set
      load-chr dup program set
      local-vars>> valid-match-vars set
      H{ } clone substitutions set
      <disjoint-set> defined-equalities set
      0 current-index set
    ] prepose with-var-names ; inline

! Replace all remaining variables with their equivalents
:: replace-equalities ( c -- c )
    c eq-constraint? [ c ]
    [ defined-equalities get :> ds
      c vars [| v | v
              v ds disjoint-set-member?
              [ v ds representative ] [ f ] if
             ] H{ } map>assoc sift-values
      c apply-substitution ] if ;

: run-chr-query ( prog query -- store )
    [ pred>constraint ] map
    [ 0 sentinel set
      [ activate-new ] each store get [ constraint>> replace-equalities ] map-values
    ] curry with-chr-prog ;

! TODO: move builtin into extra vocab?

ALIAS: == test-eq
ALIAS: ==! add-equal
