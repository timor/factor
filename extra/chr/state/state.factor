USING: accessors arrays assocs assocs.extras chr chr.programs classes.algebra
combinators.short-circuit hash-sets kernel linked-assocs lists make math
namespaces quotations sequences sets sorting terms typed words ;

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
M: chr-suspension type>> constraint>> constraint-type ; inline
M: chr-suspension args>> constraint>> constraint-args ; inline
M: chr-suspension constraint-args args>> ; inline

DEFER: activate-new

: local-var? ( variable -- ? )
    [ program get local-vars>> in? ] [ f ] if* ;

DEFER: reactivate
:: wake-equal ( v k -- )
    store get [| id sus |
               sus vars>> :> vs
               { [ v vs in? ] [ k vs in? ] } 0||
               [ id reactivate ] when
    ] assoc-each ;

: known? ( obj -- ? )
    dup term-var? [ ?ground-value ] when
    term-var? not ; inline

: known ( obj -- val )
    ?ground-value ;

! NOTE: Using Store-wide replacement for now...

DEFER: alive?

:: wakeup-set ( v k -- ids )
    store get [ vars>> :> vs { [ v vs in? ] [ k vs in? ] } 0|| ] filter-values
    keys ;

: equate-in-store ( v1 v2 -- )
    assume-equal  ;

TUPLE: equiv-activation { eqs read-only } ;
C: <equiv-activation> equiv-activation

: add-2-equal ( value key -- new )
    2dup [ local-var? ] either?
    [ "equating locals!" throw ] when
    2dup = [ 2drop f ]
    [ <eq-constraint> ] if ;
    ! [ 2dup wakeup-set <equiv-activation> ] if ;

: update-vars! ( id -- )
    dup alive?
    [ store get at dup constraint>> vars
      f lift vars
      >>vars drop ]
    [ drop ] if ;

: add-equal ( assoc -- new )
    [ add-2-equal ] { } assoc>map sift <equiv-activation> ;
    ! [ [ [ a>> ] [ b>> ] bi equate-in-store ] each ]
    ! [
    !     [ wakeup>> ] gather [ alive? ] filter
    !     [ dup update-vars! reactivate ] each
    !     ! [ wakeup>> members [ dup update-vars! reactivate ] each ] each
    ! ]
    ! [ [ [ a>> ] [ b>> ] bi 2array \ = prefix 1array ] map ] tri ;
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
    ! FIXME: This is to make sure any representatives get in! That stuff is really meh...
    ! f lift
    chr-suspension new swap
    [ >>constraint ]
    [ vars members >>vars ] bi
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

GENERIC: lookup ( ctype -- seq )

M: chr-constraint lookup
    constraint-type store get [ type>> = ] with filter-values ;

M: chr-sub-pred lookup
    class>> store get [ type>> swap class<= ] with filter-values ;

:: check/update-history ( rule-id trace -- ? )
    trace keys :> matched
    matched natural-sort rule-id prefix :> sig
    matched store get extract-keys values sift :> stored-cs
    sig stored-cs [ hist>> in? ] with all?
    [ f ]
    [ stored-cs [ [ sig suffix ] change-hist drop ] each t ] if ;

<PRIVATE
SYMBOL: current-bindings
PRIVATE>

: check-guards ( rule-id bindings -- ? )
    dup current-bindings set-global
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

! : start-match ( var-term arg-term -- subst )
!     2array 1array H{ } clone swap solve-next ;
:: try-schedule-match ( bindings arg-spec susp -- bindings )
    bindings
    susp constraint-args :> args
    arg-spec chr-sub-pred?
    [ susp constraint>> arg-spec var>> bindings set-at
      arg-spec args>> args >list
    ]
    [ clone arg-spec args ] if
    2array 1array solve-next ; inline

! : match-constraint ( bindings args constraint -- bindings )
!     over chr-sub-pred? [ break ] when
!     constraint-args dup chr-sub-pred? [ break ] when
!     swap 2array 1array solve-next ; inline

! Every level is passed the following info:
! rule-id { { id0 keep0 } ...{ id1 keep1} } bindings
:: (run-occurrence) ( rule-id trace bindings partners vars -- )
    partners empty? [
        trace [ drop alive? ] assoc-all?
        [ rule-id trace bindings fire-rule ] when
    ] [
        partners unclip-slice :> ( rest next )
        next first2 :> ( keep-partner pc )
        pc lookup
        [| sid sc |
         { [ sid trace key? not ] [ sc alive>> ] } 0&& [
             ! vars valid-match-vars [
                 bindings pc constraint-args sc try-schedule-match
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
    H{ } clone arg-vars c try-schedule-match
        [ partners vars (run-occurrence) ] [ 2drop ] if*
    ! ] with-variable
    ;

SYMBOL: sentinel

: recursion-check ( -- )
    ! sentinel get 5000 > [ "runaway" throw ] when
    sentinel get 500 > [ "runaway" throw ] when
    sentinel inc ;

! TODO: check if that is needed to make sure tail recursion works!
! Don't reactivate ourselves, don't reactivate more than once!
: activate ( id -- )
    recursion-check
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

M: equiv-activation pred>constraint ;
: update-eq-constraint-vars ( eqc -- eqc )
    dup rhs>> vars [ ?ground-value ] map members >>subsumed-vars ;

: eq-wakeup-set ( eq-constraint -- ids )
    [ rhs>> store get [ vars>> in? [ , ] [ drop ] if ] with assoc-each ] { } make ;

:: update-susp-vars! ( eqc susp -- eqc )
    eqc lhs>> :> changed
    [ susp vars>> [ dup changed = [ drop eqc subsumed-vars>> % ] [ , ] if ] each ] { } make susp swap >>vars ;

: update-wakeup-set-vars ( eq-constraint -- ids )
    dup eq-wakeup-set
    [ store get swap [ of update-susp-vars! drop ] 2with each ] keep ;

: equiv-wakeup-set ( seq -- ids )
    [ update-wakeup-set-vars ] gather ;

M: equiv-activation activate-new
    eqs>>
    [ [ [ lhs>> ] [ rhs>> ] bi assume-equal ] each ]
    [ [ update-eq-constraint-vars activate-new ] each ]
    [ equiv-wakeup-set [ reactivate ] each ] tri ;

M: eq-constraint activate-new
    builtins store get at constraint>> push ;

M: sequence activate-new
    [ activate-new ] each ;

M: constraint activate-new
    ! recursion-check
    create-chr activate ;

M: generator activate-new
    [ body>> ]
    ! [ vars>> [ dup dup word? [ name>> ] when uvar <gvar>
    [ vars>> [ dup dup word? [ name>> ] when uvar <term-var>
             ] H{ } map>assoc ] bi lift
    activate-new ;

M: true activate-new drop ;

M: callable activate-new
    ! recursion-check
    call( -- new )
    pred>constraint
    ! reactivate-all
    activate-new ;

! TODO: check whether in-place store modification is sound
M:: chr-suspension apply-substitution* ( subst c -- c )
    c [ subst swap apply-substitution* ] change-constraint
    [ members subst lift >hash-set ] change-vars ;

M: builtin-suspension apply-substitution* nip ;

! : with-chr-prog ( prog quot -- )
!     [ LH{ } clone store set
!       <builtins-suspension> builtins store get set-at
!       load-chr dup program set
!       local-vars>> valid-match-vars set
!       H{ } clone substitutions set
!       ! <disjoint-set> defined-equalities set
!       0 current-index set
!     ] prepose with-var-names ; inline

: init-chr-scope ( prog -- )
    LH{ } clone store set
    <builtins-suspension> builtins store get set-at
    load-chr dup program set
    local-vars>> valid-match-vars set
    check-vars? on
    0 current-index set
    H{ } clone var-names set
    ;

! This should ensure catching terms without a solution!
! : solve-eq-constraints ( store -- )
!     builtins of constraint>> dup .
!     [ constraint-args first2 f lift
!       2array ] map dup .
!     f defined-equalities-ds [ valid-match-vars off ground-values off
!       dup [ valid-match-vars off ground-values off solve-problem ] with-term-vars drop
!     ] with-global-variable
!     ;

: run-chr-query ( prog query -- store )
    [ pred>constraint ] map
    2dup 2array
    [
      0 sentinel set
      H{ } clone ground-values set
      swap
      init-chr-scope
      [ activate-new ] each
      ! ground-values get .
      store get
      ! dup solve-eq-constraints
      [ constraint>>
        over builtins = [ f lift ] unless
      ] assoc-map
    ] with-term-vars
    f current-bindings set-global ;

: run-chrat-query ( query -- store )
    prepare-query run-chr-query ;


: query-with ( solver query -- store )
     prepare-query-with run-chr-query ;

ALIAS: == test-eq
ALIAS: ==! make-equal
