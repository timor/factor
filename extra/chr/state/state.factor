USING: accessors arrays assocs assocs.extras chr chr.parser chr.programs
combinators combinators.short-circuit disjoint-sets hash-sets hashtables kernel
linked-assocs match math namespaces quotations sequences sets typed types.util
words ;

IN: chr.state

TUPLE: chr-state stack store builtins trace n vars ;

FROM: namespaces => set ;
FROM: syntax => _ ;

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

TUPLE: builtin-suspension < chr-suspension type ;
: <builtins-suspension> ( -- obj )
    builtin-suspension new
    V{ } clone >>constraint ;

SLOT: type
SLOT: args
M: chr-suspension type>> constraint>> constraint-type ;
M: chr-suspension args>> constraint>> constraint-args ;

! This is an interface var, which can change during rule processing
! FIXME Unused
SYMBOL: substitutions
SINGLETON: rule-fail

SYMBOL: ground-values

: maybe-add-atom ( x ds -- )
    2dup disjoint-set-member?
    [ 2drop ] [ add-atom ] if ; inline

: local-var? ( variable -- ? )
    [ program get local-vars>> in? ] [ f ] if* ;

:: define-ground-value ( var value ds -- )
    var ds 2dup maybe-add-atom
    representative ground-values get
    [| old | old [ old value = [ old ] [ "contradiction" throw ] if ]
     [ value ] if
    ] change-at ;

: maybe-define-ground-value ( v1 v2 ds -- )
    over match-var? [ swapd ] when
    over match-var? [ 3drop ] [
        define-ground-value
    ] if ;

DEFER: activate-new
! Interface for builtin solvers!
: assume-equal ( a b ds -- )
    2over [ match-var? ] both?
    [
        {
            [ nipd maybe-add-atom ]
            [ nip maybe-add-atom ]
            [ equate ]
        }
        3cleave
    ] [ maybe-define-ground-value ] if ;

! :: equiv-in? ( v1 v2 set -- ? )


DEFER: reactivate
:: wake-equal ( v k -- )
    store get [| id sus |
               sus vars>> :> vs
               { [ v vs in? ] [ k vs in? ] } 0||
               [ id reactivate ] when
    ] assoc-each ;

! Interface for builtin solving
! NOTE: This tests alpha-equality
: test-eq ( lhs rhs -- ? )
    solve-eq { [  ] [ assoc-empty? ] } 1&& ;

! Keep track of ground terms for equivalence classes
: ?ground-value ( var -- val/key )
    ground-values get ?at drop ;

: known? ( obj -- ? )
    dup match-var? [ ?ground-value ] when
    match-var? not ; inline

: ?representative ( var -- var )
    { [ defined-equalities get representative ] [  ] } 1|| ;

: known ( obj -- val )
    ?ground-value ;
    ! ?representative ?ground-value ;
    ! dup match-var? [ defined-equalities get representative ?ground-value ] when
! dup [ "unknown" throw ] unless ;

! NOTE: Using Store-wide replacement for now...

:: wakeup-set ( v k -- ids )
    store get [ vars>> :> vs { [ v vs in? ] [ k vs in? ] } 0|| ] filter-values
    keys ;

DEFER: apply-substitution
: replace-in-store ( v1 v2 -- )
    dup match-var? [ swap ] unless associate
    store [ [ apply-substitution ] with map-values ] change
    ;

: equate-in-store ( v1 v2 -- )
    [ replace-in-store ]
    [ defined-equalities get assume-equal ] 2bi ;

TUPLE: equiv-activation { a read-only } { b read-only } { wakeup read-only } ;
C: <equiv-activation> equiv-activation

: add-2-equal ( value key -- new )
    2dup [ local-var? ] either?
    [ "equating locals!" throw ] when
    2dup = [ 2drop f ]
    [ 2dup wakeup-set <equiv-activation> ] if ;



: add-equal ( assoc -- new )
    [ add-2-equal ] { } assoc>map sift
    [ [ [ a>> ] [ b>> ] bi equate-in-store ] each ]
    [ [ wakeup>> [ reactivate ] each ] each ]
    [ [ [ a>> ] [ b>> ] bi 2array \ = prefix 1array ] map ] tri ;
    ! 2dup [ local-var? ] either?
    ! [ "equating locals!" throw ] when
    ! 2dup = [ 2drop f ]
    ! [ 2dup wakeup-set
    !   2over equate-in-store
    !   [ reactivate ] each
    !   2array \ = prefix 1array
    ! ] if ;
    ! 2dup test-eq
    ! [ 2drop f ]
    ! [
    !     {
    !         ! [ maybe-define-ground-value ]
    !         [ defined-equalities get assume-equal ]
    !         [ 2array \ = prefix 1array ]
    !         [ wake-equal ]
    !     }
    !     2cleave ] if ;

ERROR: cannot-make-equal lhs rhs ;
: unify ( t1 t2 -- subst )
    valid-match-vars [ solve-eq ] with-variable-off ;

: make-equal ( lhs rhs -- new )
    2dup unify
    [ 2nip add-equal ]
    [ cannot-make-equal ] if* ;

TYPED: create-chr ( c: constraint -- id )
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
    matched natural-sort rule-id prefix :> sig
    matched store get extract-keys values sift :> stored-cs
    sig stored-cs [ hist>> in? ] with all?
    [ f ]
    [ stored-cs [ [ sig suffix ] change-hist drop ] each t ] if ;

: check-guards ( rule-id bindings -- ? )
    [ program get rules>> nth ] dip
    swap guard>> [ test-constraint ] with all? ;

: substitute-ground-values ( subst -- subst )
    [ ?ground-value ] map-values ;

: apply-substitution ( subst constraint -- constraint )
    ! [ substitute-ground-values ] dip
    apply-substitution* ;

! TODO: Don't use t as special true value in body anymore...
: run-rule-body ( rule-id bindings -- )
    [ program get rules>> nth ] dip
    ! swap body>> dup t =
    ! [ 2drop ] [ [ apply-substitution activate-new ] with each ] if ;
    swap body>> [ apply-substitution activate-new ] with each ;

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
:: (run-occurrence) ( rule-id trace bindings partners vars -- )
    partners empty? [
        trace [ drop alive? ] assoc-all?
        [ rule-id trace bindings fire-rule ] when
    ] [
        partners unclip-slice :> ( rest next )
        next first2 :> ( keep-partner pc )
        pc constraint-type lookup
        [| sid sc |
         { [ sid trace key? not ] [ sc alive>> ] } 0&& [
             ! vars valid-match-vars [
                 bindings sc args>> pc match-constraint
             ! ] with-variable
             :> bindings1
             bindings1 [
                 rule-id trace sid keep-partner 2array suffix bindings1 rest vars (run-occurrence)
             ] when
         ] when
        ] assoc-each
    ] if ;


:: run-occurrence ( c schedule --  )
    c id>> :> active-id
    schedule [ occurrence>> first ] [ arg-vars>> ] [ partners>> ] tri
    :> ( rule-id arg-vars partners )
    rule-id active-id schedule keep-active?>> 2array 1array
    schedule rule-vars>> ! c vars>> union
    :> vars ! valid-match-vars set
    ! [
        ! vars valid-match-vars [ arg-vars c args>> start-match ] with-variable
    arg-vars c args>> start-match
        [ partners vars (run-occurrence) ] [ 2drop ] if*
    ! ] with-variable
    ;

SYMBOL: sentinel

: recursion-check ( -- )
    ! sentinel get 500 > [ "runaway" throw ] when
    sentinel inc ;

! TODO: check if that is needed to make sure tail recursion works!
! Don't reactivate ourselves, don't reactivate more than once!
: activate ( id -- )
    store get at
    ! dup activated>>
    ! [ drop ]
    ! [
    !     dup t >>activated
    !     recursion-check
        dup type>> program get schedule>> at
        [ run-occurrence ] with each
    !     f >>activated drop
    ! ] if
    ;

GENERIC: activate-new ( c -- )
M: eq-constraint activate-new
    builtins store get at constraint>> push ;

M: sequence activate-new
    [ activate-new ] each ;

M: constraint activate-new
    recursion-check
    create-chr activate ;

M: generator activate-new
    [ body>> ]
    ! [ vars>> [ dup dup word? [ name>> ] when uvar <gvar>
    [ vars>> [ dup dup word? [ name>> ] when uvar <term-var>
             ] H{ } map>assoc ] bi lift
    activate-new ;

M: true activate-new drop ;

M: callable activate-new
    recursion-check
    call( -- new )
    pred>constraint
    ! reactivate-all
    activate-new ;

! TODO: check whether in-place store modification is sound
M:: chr-suspension apply-substitution* ( subst c -- c )
    c [ subst swap apply-substitution* ] change-constraint
    [ members subst lift >hash-set ] change-vars ;

M: builtin-suspension apply-substitution* nip ;

: with-chr-prog ( prog quot -- )
    [ LH{ } clone store set
      <builtins-suspension> builtins store get set-at
      load-chr dup program set
      local-vars>> valid-match-vars set
      H{ } clone substitutions set
      <disjoint-set> defined-equalities set
      0 current-index set
    ] prepose with-var-names ; inline

! Replace all remaining variables with their equivalents
:: replace-equalities ( c -- c )
    c builtin-suspension? [ c constraint>> ]
    [ c constraint>> :> c
      defined-equalities get :> ds
      c vars [| v | v
              v ds disjoint-set-member?
              [ v ds representative
                ?ground-value
              ] [ f ] if
             ] H{ } map>assoc sift-values
      c apply-substitution ] if ;

: run-chr-query ( prog query -- store )
    [ pred>constraint ] map
    [ 0 sentinel set
      H{ } clone ground-values set
      [ activate-new ] each
      store get
      ! replace-equalities
      [ replace-equalities ] map-values
    ] curry with-chr-prog ;

: run-chrat-query ( query -- store )
    prepare-query run-chr-query ;

! TODO: move builtin into extra vocab?

ALIAS: == test-eq
ALIAS: ==! make-equal
