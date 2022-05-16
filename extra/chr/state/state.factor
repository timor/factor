USING: accessors arrays assocs assocs.extras chr chr.programs
chr.programs.incremental classes.algebra combinators.private
combinators.short-circuit hash-sets kernel lists make math math.combinatorics
namespaces quotations sequences sets sorting terms typed words ;

IN: chr.state

FROM: namespaces => set ;
FROM: syntax => _ ;

! SYMBOLS: program exec-stack store builtins match-trace current-index ;
SYMBOLS: program exec-stack store match-trace current-index ;

! Operational interface
TUPLE: chr-suspension
    constraint id alive activated stored hist vars from-rule cond ;

TUPLE: solver-state builtins store ;

: <solver-state> ( -- obj )
    <eq-disjoint-set> H{ } clone solver-state boa ;

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
SYMBOL: queue

: local-var? ( variable -- ? )
    [ program get local-vars>> in? ] [ f ] if* ;

! DEFER: reactivate
! :: wake-equal ( v k -- )
!     store get [| id sus |
!                sus vars>> :> vs
!                { [ v vs in? ] [ k vs in? ] } 0||
!                ! [ id reactivate ] when
!                [ queue [  ] ] when
!     ] assoc-each ;

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
    ! 2dup [ local-var? ] both?
    [ "equating locals!" throw ] when
    ! <eq-constraint> ;
    ! 2dup eq? [ 2drop f ]
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

ERROR: cannot-make-equal lhs rhs ;
! TODO: not entirely sure why we need this, probably because we don't have the
! constraint's bodies variables in scope?
: unify ( t1 t2 -- subst )
    valid-match-vars [ solve-eq ] with-variable-off ;

: make-equal ( lhs rhs -- new )
    2dup unify
    [ 2nip add-equal ]
    [ cannot-make-equal ] if* ;

: store-chr ( chr-susp -- )
    dup id>> store get set-at ; inline

TYPED: create-chr ( from-rule c: constraint -- id )
    ! FIXME: This is to make sure any representatives get in! That stuff is really meh...
    f lift
    chr-suspension new swap
    [ >>constraint
      swap >>from-rule
    ]
    [ vars members >>vars ] bi
    t >>alive
    ! current-index [ 0 or 1 + dup ] change-global [ >>id ] keep
    current-index counter [ >>id ] keep
    [ store-chr ] dip ;

: alive? ( id -- ? )
    store get at [ alive>> ] [ f ] if* ;

: enqueue ( items -- )
    queue [ append ] change ;

DEFER: activate
: reactivate ( ids -- )
    [ alive? ] filter [ enqueue ] when* ;
    ! dup alive? [ activate ] [ drop ] if ;

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

M: as-pred lookup pred>> lookup ;

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
    [ dup program get rules>> nth ] dip
    ! swap body>> dup t =
    ! [ 2drop ] [ [ apply-substitution activate-new ] with each ] if ;
    ! swap body>> [ apply-substitution activate-new ] 2with each ;
    swap body>> [ apply-substitution ] with map
    f current-bindings set-global
    ! [ activate-new ] with each
    activate-new
    ;

: simplify-constraints ( trace -- )
    [ [ drop ] [ kill-chr ] if ] assoc-each ;

: fire-rule ( rule-id trace bindings -- )
    { [ nip check-guards ]
      [ drop check/update-history ]
      [ drop nip simplify-constraints t ]
      [ nip run-rule-body t ]
    } 3&& drop ;

GENERIC: match-constraint ( bindings suspension match-spec -- bindings )

M: chr-sub-pred match-constraint
    args>> swap constraint-args >list 2array 1array solve-next ;
M: as-pred match-constraint
    ! [ [ constraint>> ] [ var>> ] bi* pick set-at ]
    [ [ constraint>> ] [ var>> ] bi* swap 2array 1array solve-next ] 2keep rot
    [ -rot pred>> constraint-args match-constraint ] [ 2drop f ] if* ;

    ! [ pred>> match-constraint ] 2bi ;
M: sequence match-constraint
    swap constraint-args 2array 1array solve-next ;

M: reflexive-parms match-constraint
    parms>> all-permutations
    [ match-constraint ] 2with map-find drop ;

! M: reflexive match-constraint
!     constraint-args
!     constraint-args [ match-constraint ]

! NOTE: match order convention:
!  rule-constraint =? store-constraint

! : start-match ( var-term arg-term -- subst )
!     2array 1array H{ } clone swap solve-next ;
DEFER: match-reflexive-head
DEFER: match-single-head
: match-head ( bindings arg-spec susp -- bindings )
    ! dup constraint>> reflexive?
    over reflexive-parms?
    [ match-reflexive-head ]
    [ match-single-head ] if ;

: match-single-head ( bindings arg-spec susp -- bindings )
    swap match-constraint ; inline
:: match-reflexive-head ( bindings arg-spec susp -- bindings )
    arg-spec parms>> all-permutations
    [| p | bindings p susp match-single-head ] map-find drop ; inline

: try-schedule-match ( bindings arg-spec susp -- bindings )
    swap match-constraint
    ! match-head
    ! bindings susp
    ! arg-spec match-constraint
    ; inline

! : match-constraint ( bindings args constraint -- bindings )
!     over chr-sub-pred? [ break ] when
!     constraint-args dup chr-sub-pred? [ break ] when
!     swap 2array 1array solve-next ; inline

! Every level is passed the following info:
! rule-id { { id0 keep0 } ...{ id1 keep1} } bindings
:: (run-occurrence) ( rule-id trace bindings partners vars -- )
    partners empty? [
        ! NOTE: unsure about this optimization here...
        trace [ drop alive? ] assoc-all?
        [ rule-id trace bindings fire-rule ] when
        ! rule-id trace bindings fire-rule
    ] [
        partners unclip-slice :> ( rest next )
        next first2 :> ( keep-partner pc )
        pc lookup sort-keys
        [| sid sc |
         ! NOTE: unsure about this optimization here
         { [ sid trace key? not ]
           [ sc alive>> ]
         } 0&& [
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
! : activate ( id -- )
!     queue [ swap prefix ] change ;

TUPLE: run-schedule c schedule ;
C: <run-schedule> run-schedule

: activate ( id -- )
    recursion-check
    ! check-integrity
    store get at
    [
        dup type>> program get schedule>> at
        [ over alive>> [ <run-schedule> ] [ 2drop f ] if ] with map enqueue
    ] when*
    ;

GENERIC: activate-new ( rule c -- )

M: equiv-activation pred>constraint ;
: update-eq-constraint-vars ( eqc -- eqc )
    dup rhs>> vars [ ?ground-value ] map members >>subsumed-vars ;

: eq-wakeup-set ( eq-constraint -- ids )
    [
        [ rhs>> store get [ vars>> in? [ , ] [ drop ] if ] with assoc-each ]
        [ lhs>> store get [ vars>> in? [ , ] [ drop ] if ] with assoc-each ] bi
    ] { } make
    ;

:: update-susp-vars! ( eqc susp -- eqc )
    eqc lhs>> :> changed
    [ susp vars>> [ dup changed = [ drop eqc subsumed-vars>> % ] [ , ] if ] each ] { } make susp swap >>vars
    ! [ f lift ] change-constraint
    ;

: update-wakeup-set-vars ( eq-constraint -- ids )
    dup eq-wakeup-set
    [ store get swap [ of update-susp-vars! drop ] 2with each ] keep ;

: equiv-wakeup-set ( seq -- ids )
    [ update-wakeup-set-vars ] gather ;

M: equiv-activation activate-new nip
    eqs>>
    [ [ [ lhs>> ] [ rhs>> ] bi assume-equal ] each ]
    [ [ update-eq-constraint-vars f swap activate-new ] each ]
    [ equiv-wakeup-set reactivate ] tri ;

! M: eq-constraint activate-new nip
!     builtins store get at constraint>> push ;
TUPLE: deferred-activation from-rule chr ;

M: eq-constraint activate-new 2drop ;
GENERIC: activate-item ( susp --  )
M: deferred-activation activate-item
    [ from-rule>> ] [ chr>> ] bi activate-new ;
M: integer activate-item activate ;
M: run-schedule activate-item
    [ c>> ] [ schedule>> ] bi
    over alive>> [ run-occurrence ]
    [ 2drop ] if ;

: run-queue ( -- )
    ! [ queue get dup empty? ] [ unclip [ queue namespaces:set ] [ activate-id ] bi* ] until ;
    [ queue get empty? ] [ queue get unclip [ queue set ] [ activate-item ] bi* ] until ;

M: sequence activate-new
    [ deferred-activation boa ] with map
    [ enqueue ] when* ;
    ! queue [ append ] change ;
    ! run-queue ;

M: constraint activate-new
    ! recursion-check
    create-chr activate ;

M: generator activate-new
    [ body>> ]
    ! [ vars>> [ dup dup word? [ name>> ] when uvar <gvar>
    [ vars>> [ dup dup word? [ name>> ] when uvar <term-var>
             ] H{ } map>assoc ] bi lift
    activate-new ;

M: true activate-new 2drop ;

M: callable activate-new ( quot effect -- )
    ! recursion-check
    ! call( -- new )
    ( -- new ) call-effect-unsafe
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
    H{ } clone store set
    ! <builtins-suspension> builtins store get set-at
    load-chr dup program set
    local-vars>> valid-match-vars set
    check-vars? on
    0 current-index set-global
    H{ } clone var-names set
    ;

: update-local-vars ( -- )
    program get local-vars>> valid-match-vars set ;

: init-dyn-chr-scope ( rules -- )
    init-chr-prog program set
    H{ } clone store set
    ! <builtins-suspension> builtins store get set-at
    update-local-vars
    check-vars? on
    0 current-index set-global
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

! SYMBOL: last-program

SYMBOL: state-id
SYMBOL: result-config

: combine-configs ( result-config -- store )
    H{ } clone H{ } clone
    [let :> ( res eqs store )
     res [| id state |
          state store>> id store set-at
          state builtins>> id eqs set-at
         ] assoc-each
     eqs store solver-state boa
    ] ;

: get-solver-state ( -- state )
    defined-equalities-ds get
    store get solver-state boa ;

: set-solver-state ( state -- )
    [ store>> store set ]
    [ builtins>> defined-equalities-ds set ] bi ;

TYPED: store-solver-config ( state: solver-state id -- )
    result-config get set-at ;

! TYPED: merge-solver-config ( state: solver-state id -- )
!     swap store>> [ [ 2array ] change-id store-chr drop ] with assoc-each ;
! NOTE: to be run in parent context
GENERIC: merge-solver-config ( key state: solver-state -- )
PREDICATE: failed-solver-state < solver-state store>> [ nip constraint>> false? ] assoc-any? ;

M: failed-solver-state merge-solver-config 2drop ;
M: solver-state merge-solver-config
    ! FIXME: might need to import existential vars here
    ! NOTE: rule history gets lost here
    store>> values store get [ value? ] curry reject
    [ constraint>> [ import-term-vars ] [ C boa ] bi ] with map
    f swap activate-new ;


! NOTE: must be done in correct scope right now (i.e. nested one)
: petrify-solver-state! ( state -- state )
    [ [ f lift ] map-values ] change-store ;

: finish-solver-state ( -- state )
    get-solver-state
    petrify-solver-state!
    [ [ constraint>> ] map-values ] change-store ;

SYMBOL: split-states

: join-states ( assoc -- )
    [ merge-solver-config ] assoc-each ;

: save-split-state ( key solver-state --  )
    2array split-states get push ;

: run-chr-query ( prog query -- state )
    [ pred>constraint ] map
    2dup 2array
    [
        V{ } clone split-states set
      ! H{ } clone result-config set
      0 state-id set-global
      0 sentinel set
      H{ } clone ground-values set
      swap
      ! init-chr-scope
      init-dyn-chr-scope
      f swap activate-new
      run-queue
      split-states get join-states
      run-queue
      finish-solver-state
      ! 0 store-solver-config
      ! result-config get combine-configs
    ] with-term-vars ;

: extend-program ( rule -- )
    program [ swap add-rule ] with change update-local-vars ;

: with-cloned-state ( state quot -- state )
    [
        [ store>>
          [ clone ] map-values
        ]
        [ builtins>> clone ] bi
    ] dip '[
        store set
        @
    ] with-var-context ; inline


: run-cases ( rule seq -- seq )
    get-solver-state swap [ swap
                            [ activate-new
                              run-queue
                              get-solver-state petrify-solver-state!
                            ] with-cloned-state
    ] 2with map ;

: maybe-invalidate-solver-state ( -- )
    get-solver-state failed-solver-state?
    [ <solver-state> set-solver-state ] when ;


! M: chr-scope activate-new (  )

! Non-return, proper or
M:: chr-or activate-new ( rule c -- )
    c constraints>>
    get-solver-state :> state
    [ state [ rule swap activate-new
           run-queue
           get-solver-state petrify-solver-state!
         ] with-cloned-state
       dup failed-solver-state? [ drop f ] when
    ] map-find [ set-solver-state ] [ drop rule false activate-new ] if
    queue off ;

! Return, but merge only at the end.  This means that the first branch will actually be
! done first?
M: chr-branch activate-new ( rule c -- )
    cases>> unzip swap
    [ run-cases ] dip
    ! Clear continuation from main branch
    <solver-state> set-solver-state queue off
    swap [ save-split-state ] 2each ;
    ! ;
    ! swap [ merge-solver-config ] 2each ;

M: false activate-new ( rule c -- )
    queue off
    call-next-method ;

! M:: chr-branch activate-new ( rule c -- )
!     get-solver-state :> parent-state
!     c cases>>
!     [ first2 :> ( tag body )
!       parent-state [
!           ! queue off
!           rule body activate-new
!           queue get .
!           run-queue
!           get-solver-state petrify-solver-state!
!       ] with-cloned-state
!       tag swap merge-solver-config
!     ] each ;

! M: And activate-new ( rule c -- )
!     [ activate-new ] with each ;

: run-chrat-query ( query -- store )
    prepare-query run-chr-query ;

: query-with ( solver query -- store )
     prepare-query-with run-chr-query ;

ALIAS: == test-eq
ALIAS: ==! make-equal
