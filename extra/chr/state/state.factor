USING: accessors arrays assocs assocs.extras chr combinators.short-circuit
kernel linked-assocs math namespaces sequences sets typed types.util ;

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
    type args id alive activated stored hist ;

! This is an interface var, which can change during rule processing
SYMBOL: substitutions
SINGLETON: rule-fail

! Interface for builtin solvers!
:: add-subst ( value key -- )
    substitutions get :> subst
    subst key ?at [ value = [ rule-fail throw ] unless ]
    [ value swap subst set-at ] if ;

TYPED: create-chr ( c: chr-constraint -- id )
    chr-suspension new swap
    [ constraint-type >>type ]
    [ constraint-args >>args ] bi
    t >>alive
    current-index [ 0 or 1 + dup ] change [ >>id ] keep
    [ store get set-at ] keep ;

GENERIC: constraint-fixed? ( chr-constraint -- ? )

: reactivate-all ( -- )
    store get [ nip dup constraint-fixed? [ drop ] [ t >>activated drop ] if ] assoc-each ;

: reactivate ( id -- )
    store get at t >>activated drop ;

:: kill-chr ( id -- )
    store get dup id of
    [ f >>alive drop id swap delete-at ]
    [ drop ] if* ;

: alive? ( id -- ? )
    store get at [ alive>> ] [ f ] if* ;

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

! TODO: Don't use t as special true value in body anymore...
DEFER: activate
: run-rule-body ( rule-id bindings -- )
    [ program get rules>> nth ] dip
    swap body>> dup t =
    [ 2drop ] [ [ swap lift activate ] with each ] if
    ;

: simplify-constraints ( trace -- )
    [ [ kill-chr ] [ drop ] if ] assoc-each ;

: fire-rule ( rule-id trace bindings -- )
    { [ nip check-guards ]
      [ drop check/update-history ]
      [ drop nip simplify-constraints t ]
      [ nip run-rule-body t ]
    } 3&& drop ;

! Every level is passed the following info:
! rule-id { { id0 keep0 } ...{ id1 keep1} } bindings
:: (run-occurrence) ( rule-id trace bindings partners -- )
    partners empty? [
        rule-id trace bindings fire-rule
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
    c args>> arg-vars solve-eq
    [ partners (run-occurrence) ] [ 2drop ] if* ;

: activate-constraint ( id -- )
    store get at
    dup type>> program get schedule>> at
    [ run-occurrence ] with each ;

SYMBOL: sentinel
: activate ( c -- )
    sentinel get
    [ 100 > [ "runaway" throw ] when
      sentinel inc ] when*
    create-chr activate-constraint ;

: with-chr-prog ( prog quot -- )
    [ LH{ } clone store set
      read-chr program set
      0 current-index set
    ] prepose with-scope ; inline

: run-chr-query ( prog query -- store )
    [ pred>constraint ] map
    [ 0 sentinel set [ activate ] each store get ] curry with-chr-prog ;
