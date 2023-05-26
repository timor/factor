USING: accessors arrays assocs assocs.extras chr chr.programs
chr.programs.incremental classes classes.algebra colors.constants
combinators.private combinators.short-circuit combinators.smart continuations
hash-sets hashtables io.styles kernel linked-assocs lists make match math
math.order math.parser namespaces persistent.assocs prettyprint
prettyprint.custom prettyprint.sections quotations sequences
sequences.generalizations sets sorting system terms typed words ;

IN: chr.state

FROM: namespaces => set ;
FROM: syntax => _ ;

SYMBOL: schedule-start-time
SYMBOL: collect-stats
: collect-stats? ( -- ? )
    collect-stats get-global ; inline
! NOTE: quot may not produce outputs!
: when-trace-stats ( quot -- )
    collect-stats? swap dup dropping if ; inline

: with-trace-stats ( quot -- )
    [ t collect-stats ] dip with-global-variable ; inline

! SYMBOLS: program exec-stack store builtins match-trace current-index ;
SYMBOLS: program exec-stack store match-trace current-index ;
! Interpret Is{ ?x ?y } predicates in contexts as extra bindings
SYMBOL: context-eqs

! Used for implementing :>> and get-context
<PRIVATE
SYMBOL: current-bindings
PRIVATE>

! Keep track of rule match counts
SYMBOL: rule-firings
SYMBOL: active-rule-firing

SYMBOL: lookup-index

DEFER: alive?

: lookup-update-index-entry ( seq -- seq )
    dup [ [ alive? ] filter! ] when
    [ f ] [ store get '[ dup _ at 2array ] map ] if-empty ; inline


: lookup-update-index ( key assoc -- seq )
    at lookup-update-index-entry ; inline
    ! [let f :> result!
    !  [ [ alive? ] filter dup result! ] change-at
    !  result [ f ]
    !  store get '[ [ dup _ at 2array ] map ] if-empty
    ! ] ; inline
SINGLETON: current-context
INSTANCE: current-context match-var
! SYMBOL: current-context

: new-context ( name quot -- )
    ! [ uvar current-context ] dip with-variable ; inline
    swap uvar current-context namespaces:set call ; inline
: no-context ( quot -- )
    ! current-context swap with-variable-off ; inline
    current-context off call ; inline
! NOTE: This only works in guards!
: get-context ( -- x )
    current-bindings get-global
    current-context of ;

! Operational interface
TUPLE: chr-suspension
    constraint id alive activated stored hist vars from-rule ctx ;

TUPLE: solver-state builtins store ;

TUPLE: susp-id < identity-tuple { number read-only } { rule read-only } { match-num read-only } ;
C: <susp-id> susp-id
: pprint-susp-id ( susp-id -- string )
    [ match-num>> ] [ number>> ] [ rule>> ] tri [ number>string ] dip
    [ number>string rot number>string "-" glue "(" ")" surround
      ! >subscript
      append ] [ nip ] if*
    ;

M: susp-id pprint*
    pprint-susp-id
    H{ { io.styles:foreground COLOR: solarized-violet } } styled-text ;

M: susp-id <=> [ number>> ] bi@ <=> ; inline

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

! ERROR: duplicate-index-value key value ;

! TODO correct destructive ops
: add-to-lookup-index ( value key assoc -- )
    over ground-value? [ "nope" throw ] unless
    2dup [ [ alive? ] filter ] change-at
    push-at ;

: maybe-store-index ( chr-susp id -- )
    swap constraint>>
    dup lookup-index-key
    ! { [  ]
    !   [ ?ground-value term-var? ] } 1&&
    [ [ class-of ] dip 2array lookup-index get add-to-lookup-index ]
    [ 2drop ] if* ; inline

: store-chr ( chr-susp -- )
    dup id>>
    2dup maybe-store-index
    store get set-at ; inline

! : rule-num ( id -- id/name )
!     [ number>string ] keep program get rules>> nth dup named-chr? [ rule-name>> "(" ")" surround " " glue ] [ drop ] if
!     "R" prepend
!     ; inline
! ! [ drop ] if ;


: new-id ( from-rule -- id )
    ! rule-id
    current-index counter swap
    active-rule-firing get
    ! dup rule-firings get at
    <susp-id> ; inline

TYPED: create-chr ( from-rule c: constraint -- id )
    dupd
    ! FIXME: This is to make sure any representatives get in! That stuff is really meh...
    f lift
    chr-suspension new swap
    [ >>constraint
      swap >>from-rule
    ]
    [ vars >>vars ] bi
    t >>alive
    current-context get >>ctx
    ! current-index [ 0 or 1 + dup ] change-global [ >>id ] keep
    ! current-index counter [ >>id ] keep
    swap new-id [ >>id ] keep
    [ store-chr ] dip ;

! TODO: this can simply be checked on key presence, or can it?
: alive? ( id -- ? )
    store get at [ alive>> ] [ f ] if* ;

! NOTE: changing to destructive semantics because of context scoping during creation.
! This needs to be taken into account when considering split-store processing?
: enqueue ( items -- )
    <reversed> queue get push-all ;

SYMBOL: reactivations

: record-reactivations ( ids -- )
    store get swap values-of reactivations get [ [ constraint>> constraint-type ] dip inc-at ] curry each ; inline

DEFER: activate
: reactivate ( ids -- )
    [ alive? ] filter dup [ record-reactivations ] when-trace-stats
    [ number>> ] sort-with
    [ enqueue ] unless-empty ;

GENERIC: on-kill-chr ( susp chr -- )
M: object on-kill-chr 2drop ;

:: kill-chr ( id -- )
    store get dup id of
    dup dup constraint>> on-kill-chr
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

! : in-context? ( susp -- ? )
!     ctx>> current-context get = ;

: sameclass-index-lookup ( class -- seq )
    lookup-index get swap
    '[ [ swap first _ eq? [ lookup-update-index-entry % ] [ drop ] if ] assoc-each ] { } make ; inline

M: chr-constraint lookup
    constraint-type sameclass-index-lookup ;

: subclass-index-lookup ( class -- seq )
    lookup-index get swap
    '[ [ swap first _ class<= [ lookup-update-index-entry % ] [ drop ] if ] assoc-each ] { } make ; inline

M: chr-sub-pred lookup
    class>> subclass-index-lookup ;

M: as-pred lookup pred>> lookup ;

! M: C lookup pred>> lookup ;

:: check/update-history ( rule-id trace -- ? )
    trace keys :> matched
    matched natural-sort rule-id prefix :> sig
    matched store get extract-keys values sift :> stored-cs
    sig stored-cs [ hist>> in? ] with all?
    [ f ]
    [ stored-cs [ [ sig suffix ] change-hist drop ] each t ] if ;

DEFER: record-schedule-end
SYMBOL: guard-fails
: (record-guard-fail) ( rule-num guard -- )
    nano-count pick "guard" record-schedule-end
    2array guard-fails get inc-at ; inline

: record-guard-fail ( rule-num guard -- )
    [ (record-guard-fail)
      nano-count schedule-start-time set-global
    ] when-trace-stats ; inline

! : check-guards ( rule-id bindings -- ? )
!     dup current-bindings set-global
!     [ program get rules>> nth ] dip
!     swap guard>> [ test-constraint ] with all? ;

:: check-guards ( rule-id bindings -- ? )
    bindings dup current-bindings set-global
    rule-id program get rules>> nth
    guard>> [
        [ test-constraint ] keep :> guard
        dup [ rule-id guard record-guard-fail ] unless
    ] with all? ;

: substitute-ground-values ( subst -- subst )
    [ ?ground-value ] map-values ;

: apply-substitution ( subst constraint -- constraint )
    ! [ substitute-ground-values ] dip
    apply-substitution* ;

: record-rule-firing ( rule-id -- )
    ! drop rule-firings counter drop ;
    [ rule-firings get inc-at ]
    [ rule-firings get at active-rule-firing set ] bi ; inline

! TODO: Don't use t as special true value in body anymore...
: run-rule-body ( rule-id bindings -- )
    over record-rule-firing
    dup current-context of current-context
    [
        [ dup program get rules>> nth ] dip
        ! swap body>> dup t =
        ! [ 2drop ] [ [ apply-substitution activate-new ] with each ] if ;
        ! swap body>> [ apply-substitution activate-new ] 2with each ;
        swap body>> [ apply-substitution ] with map
        f current-bindings set-global
        ! [ activate-new ] with each
        activate-new
    ] with-variable
    ;

! : maybe-inhibit-remove ( trace bindings -- trace )
!     current-context of
!     [ [| id keep? ctx |
!        keep?
!        [ id t ]
!        [ id dup store get at
!          ctx>> ctx = not
!        ] if
!       ] curry assoc-map ] when* ;

: simplify-constraints ( trace bindings -- )
    ! maybe-inhibit-remove
    drop
    [ [ drop ] [ kill-chr ] if ] assoc-each ;

ERROR: more-partners rule-firing more ;

TUPLE: rule-firing rule-id bindings ;
C: <rule-firing> rule-firing

: schedule-fire-cont ( rule-id bindings -- )
    <rule-firing> '[ _ swap more-partners ] callcc0 ;

: fire-rule ( rule-id trace bindings -- )
    { [ nip check-guards ]
      [ [ nano-count 2nip swap "run" record-schedule-end ] when-trace-stats t ]
      [ drop check/update-history ]
      [ [ drop ] 2dip simplify-constraints t ]
      [ nip
        schedule-fire-cont
        ! run-rule-body
        t ]
    } 3&& drop
    ;

! The thing dispatched on is in the partner slot in the schedule
GENERIC: match-constraint ( bindings suspension match-spec -- bindings )

: add-bindings ( bindings rhs lhs -- bindings )
    swap 2array 1array solve-next ;

! Version that extends context
! : combine-context ( susp-ctx -- new-ctx ? )
!     current-context get
!     2dup = [ drop t ]
!     [ 2dup and [ drop f ] [ or t ] if ] if ;
! C1 + f -> C1
! C1 + C2 -> mismatch
! f + f -> f
! f + C1 -> C1
: resolve-match-context ( bindings susp-ctx -- bindings/f )
    current-context pick at
    2dup and [
        = [ drop f ] unless
    ] [ or
        [ current-context rot new-at ] when*
    ] if ;

! This basically implements an implicit guard on the "invisible" context arg of
! every stored constraint
:: match-constraint-in-context ( bindings susp match-spec -- bindings )
    ! ! match-spec C? [ bindings susp match-spec match-constraint ]
    ! ! [
    ! ! bindings susp ctx>> combine-context?
    ! !     [ susp match-spec match-constraint ] [ f ] if*
    ! ! ] if
    bindings susp ctx>> resolve-match-context
    [ susp match-spec match-constraint ] [ f ] if*
    ! current-context bindings at susp ctx>> =
    ! [ bindings susp match-spec match-constraint ] [ f ] if
    ; inline

! We match a suspension in C1 against a { C ?x ... }
! When matching a C constraint, we need to turn the context bindings themselves off
! to make sure we see other partners
! M:: C match-constraint ( binds susp mspec -- bindings )
!     ! binds current-context mspec cond>> add-bindings
!     ! [ susp mspec then>> constraint-args match-constraint-in-context ] [ f ] if* ;
!     current-context binds pluck-at
!     susp ctx>> mspec cond>> add-bindings
!     [ susp mspec then>> constraint-args match-constraint ] [ f ] if* ;

M: chr-sub-pred match-constraint
    args>> swap constraint-args >list add-bindings ;

M: as-pred match-constraint
    ! [ [ constraint>> ] [ var>> ] bi* pick set-at ]
    [ [ constraint>> ] [ var>> ] bi* add-bindings ] 2keep rot
    [ -rot pred>> constraint-args match-constraint ] [ 2drop f ] if* ;

    ! [ pred>> match-constraint ] 2bi ;
M: sequence match-constraint
    swap constraint-args 2array 1array solve-next ;

M: any-match match-constraint
    cases>> [ match-constraint ] 2with map-find drop ;

! M: reflexive-parms match-constraint
!     parms>> all-permutations
!     [ match-constraint ] 2with map-find drop ;

! M: reflexive match-constraint
!     constraint-args
!     constraint-args [ match-constraint ]

! NOTE: match order convention:
!  rule-constraint =? store-constraint

! : start-match ( var-term arg-term -- subst )
!     2array 1array H{ } clone swap solve-next ;
! DEFER: match-reflexive-head
DEFER: match-single-head
: match-head ( bindings arg-spec susp -- bindings )
    ! dup constraint>> reflexive?
    match-single-head ; inline
    ! over reflexive-parms?
    ! [ match-reflexive-head ]
    ! [ match-single-head ] if ;

: match-single-head ( bindings arg-spec susp -- bindings )
    swap match-constraint ; inline
! :: match-reflexive-head ( bindings arg-spec susp -- bindings )
!     arg-spec parms>> all-permutations
!     [| p | bindings p susp match-single-head ] map-find drop ; inline


: try-schedule-match ( bindings arg-spec susp -- bindings )
    swap match-constraint-in-context
    ! swap match-constraint
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

! Most specific conditions get priority if a context is provided
! pair: { store-id suspension }
! :: cond<=> ( pair1 pair2 ctx -- <=> )
!     ctx
!     [ pair1 second ctx>> :> ctx1
!       pair2 second ctx>> :> ctx2
!       ctx1 [ ctx2 [ +eq+ ] [ +lt+ ] if ]
!       [ ctx2 [ +gt+ ] [ +eq+ ] if ] if
!     ]
!     [ +eq+ ] if ;

! : sort-lookup ( assoc bindings -- alist )
!     [ sort-keys ] [ current-context of ] bi*
!     [ cond<=> ] curry sort ;

! TUPLE: schedule-cont rule-id trace bindings partners vars ;
! C: <schedule-cont> schedule-cont

! TODO: why the hell does this work an what does it do?
! Here's the analysis: If, during the run of an occurrence, the active store constraint is
! - to be kept
! - still alive
! - has been reactivated
! this occurrence run will be aborted.  Since the reactivation marker has been cleared
! during the start of this occurrence run, it must have been triggered to be reactivated
! during the execution of the constraint body.  If so, every guard and rule has already been checked.


! Same if the original constraint isn't live anymore
! Note that it should be possible to extend this to the partner constraints?
: live-trace? ( trace -- ? )
    store get [ nip key? ] curry assoc-all? ; inline

:: recursive-drop? ( trace -- ? )
    trace first first2 :> ( id keep? )
    keep? [ id store get at
            ! Drop after reactivated
            [ activated>> ]
            [ ! Early Drop
                t ] if*
    ] [ f ] if ; inline

: chr-index-key ( chr -- key/f )
    [ class-of ] [ lookup-index-key ] bi
    [ 2array ] [ drop f ] if* ; inline

! : lookup-key-maybe-delete ( key -- id/assoc )
!     dup lookup-index get at
!     [ dup alive?
!       [ nip dup store get at 2array 1array ]
!       [
!           ! break
!           drop lookup-index get delete-at f ] if
!     ]
!     [ drop f ] if* ; inline

! TODO: correctly support as-pred lookup, and calculate the key more cleverly on chr-susp info?
: try-index-lookup ( key bindings -- seq/f )
    lift lookup-index get lookup-update-index ;
    ! [ lookup-key-maybe-delete ]
    ! [ f ] if* ; inline

SYMBOL: occurrence-times

: record-schedule-end ( time key1 event-key -- )
    [ schedule-start-time get-global -
      ! FIXME: remove once proven
      dup 0 < [ "schedule recorder error" throw ] when
    ] 2dip swap
    occurrence-times get [ [ H{ } clone ] unless* [ at+ ] keep ] change-at ;

! : extract-rule-number ( occ trace -- num )
!     [ nip first first rule>> ] [ first ] if* ; inline

SYMBOL: occurrence-mismatches
: (record-mismatch) ( occ trace susp -- )
    ! [ length ] [ constraint>> constraint-type ] bi* occurrence-mismatches get push-at ; inline
    [ length ] [ constraint>> constraint-type ] bi* occurrence-mismatches get [
        [ H{ } clone ] unless*
        [ swapd push-at ] keep
    ] change-at ; inline

: record-mismatch ( occ trace susp -- ) [ (record-mismatch) ] when-trace-stats ; inline

! FIXME: if we don't have ctx in the first place, don't even try!
: filter-lookup-context ( ctx assoc -- assoc )
    [ ctx>> { [ and ] [ = not ] } 2&& ] with reject-values ;

:: (run-occurrence) ( rule-id trace bindings partners vars -- )
    trace { [ recursive-drop? not ] [ live-trace? ] } 1&&
    ! [ break ]
    [ partners empty? [
        ! NOTE: unsure about this optimization here...
          ! FIXME: shouldnt be needed after live-trace? check above
        trace [ drop alive? ] assoc-all?
        [
            rule-id trace bindings fire-rule
            ! NOTE: counting this as starting a new search
            nano-count schedule-start-time set-global
        ] [ "shouldn't happen" throw ] if
    ] [
        partners unclip-slice :> ( rest next )
        next first2 :> ( keep-partner pc )
        ! lookup returns an { id chr-susp } assoc
        pc chr-index-key :> ikey
        ikey [ bindings try-index-lookup ]
        [ pc lookup ] if*
        bindings current-context of [ swap filter-lookup-context ] when*
        ! NOTE: having the store as linked hashtable seems to ensure stability here, even
        ! with index lookup
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
             ] [
                 ! FIXME: re-integrate into record-mismatch!
                 [ nano-count rule-id "mismatch" record-schedule-end ] when-trace-stats
                 rule-id trace sc record-mismatch
                 nano-count schedule-start-time set-global
             ] if
         ] when
        ] assoc-each
      ] if ]
    when
    ;

! Entry point of a CHR occurrence
! Sets up the initial constraint arguments
:: run-occurrence ( susp schedule --  )
    susp id>> :> active-id
    ! susp ctx>> current-context set
    schedule [ occurrence>> first ] [ arg-vars>> ] [ partners>> ] tri
    :> ( rule-id arg-vars partners )
    rule-id active-id schedule keep-active?>> dup :> keep?
    2array 1array dup :> trace
    schedule rule-vars>> ! susp vars>> union
    :> vars ! valid-match-vars set
    ! if propagate-transition, reset activated field
    f susp activated<<
    ! [
        ! vars valid-match-vars [ arg-vars susp args>> start-match ] with-variable
    ! Initialize the occurrence bindings with the required context if one was stored in ctx>> of the susp
    ! Not always use context! If there is no context specification, don't treat as problem
    nano-count schedule-start-time set-global
    current-context susp ctx>> [ swap associate ] [ drop H{ } clone ] if* arg-vars susp try-schedule-match
    ! Always use context!  The default context is f
    ! current-context susp ctx>> swap associate arg-vars susp try-schedule-match
    ! H{ } clone arg-vars susp try-schedule-match
    [ partners vars (run-occurrence) ]
    [ [ nano-count rule-id "mismatch" record-schedule-end ] when-trace-stats
      2drop schedule occurrence>> f susp record-mismatch
      nano-count schedule-start-time set-global

     ] if*
    ! ] with-variable
    ;

SYMBOL: sentinel

! : recursion-check ( -- )
!     ! sentinel get 5000 > [ "runaway" throw ] when
!     sentinel get 500 > [ "runaway" throw ] when
!     sentinel inc ;

: recursion-check ( -- )
    queue get length 1000 > [ "runaway" throw ] when ;
    ! ! sentinel get 5000 > [ "runaway" throw ] when
    ! sentinel get 500 > [ "runaway" throw ] when
    ! sentinel inc ;

! TODO: check if that is needed to make sure tail recursion works!
! Don't reactivate ourselves, don't reactivate more than once!
! : activate ( id -- )
!     queue [ swap prefix ] change ;

TUPLE: run-schedule c schedule ;
C: <run-schedule> run-schedule
TUPLE: set-reactivated id ;
C: <set-reactivated> set-reactivated

: activate ( id -- )
    recursion-check
    ! check-integrity
    store get at
    [
        f >>activated
        dup type>> program get schedule>> at
        ! dup length 1 > [ break ] when
        [ over alive>> [ <run-schedule> ] [ 2drop f ] if ] with map enqueue
    ] when*
    ;

: reactivate-item ( id -- )
    [ <set-reactivated> 1array enqueue ]
    [ activate ] bi ;

! This is called on all body constraints after rule firing.  Runs to completion
! in the context of the rule bodies, but will created deferred objects and enqueue them.
GENERIC: activate-new ( rule c -- )

! M: C activate-new [ cond>> current-context set ] [ then>> activate-new ] bi ;
! M: C activate-new
!     dup cond>> current-context [ then>> activate-new ] with-variable ;

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
! from-rule is { rule-id firing-number }
TUPLE: deferred-activation from-rule chr ctx ;

M: eq-constraint activate-new 2drop ;
GENERIC: activate-item ( susp --  )
M: deferred-activation activate-item
    ! dup ctx>> current-context set
    ! [ from-rule>> ] [ chr>> ] bi activate-new ;
    dup ctx>> current-context [
        [ from-rule>>
        first2 active-rule-firing set
        ] [ chr>> ] bi activate-new
    ] with-variable
    ;

! M: integer activate-item
!     ! If we have enqueued it several times, then we basically bumped it up, so no need to run it repeatedly
!     [ queue get remove! drop ]
!     [ reactivate-item ] bi ;
M: susp-id activate-item
    ! If we have enqueued it several times, then we basically bumped it up, so no need to run it repeatedly
    [ queue get remove! drop ]
    [ reactivate-item ] bi ;

M: set-reactivated activate-item
    ! [ queue get remove! drop ]
    ! [ id>> store get ?at [ t >>activated ] when drop ] bi ;
    id>> store get ?at [ t >>activated ] when drop ;

! This is the main entry point to actually start a constraint schedule
M: run-schedule activate-item
    [ c>> ] [ schedule>> ] bi
    over { [ alive>> ]
           ! Drop after Reactivation check
           [ activated>> not ]
    } 1&& [ run-occurrence ]
    [ 2drop ] if ;

M: rule-firing activate-item
    [ rule-id>> ] [ bindings>> ] bi run-rule-body ;

M: more-partners activate-item
    more>> continue ;


! If we catch a bailout, then we throw away the tried suspension, and replace it with queuing the
! continuation and (first) the actual rule firing
: run-queue ( -- )
    ! [ queue get dup empty? ] [ unclip [ queue namespaces:set ] [ activate-id ] bi* ] until ;
    [ queue get empty? ] [ queue get pop
                           [ activate-item ]
                           [ dup more-partners?
                             [ nip [ queue get push ] [ rule-firing>> queue get push ] bi ]
                             [ rethrow ] if
                           ] recover
    ] until ;

: <deferred-activation> ( from-rule chr ctx -- obj )
    [ dup rule-firings get at 2array ] 2dip deferred-activation boa ; inline

M: sequence activate-new
    current-context get [ <deferred-activation> ] curry with map
    [ enqueue ] when* ;
    ! queue [ append ] change ;
    ! run-queue ;

M: constraint activate-new
    ! recursion-check
    ! runaway-check
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

: update-local-vars ( -- )
    program get local-vars>> current-context suffix
    valid-match-vars set ;

: init-chr-scope ( rules -- )
    init-chr-prog program set
    LH{ } clone store set
    LH{ } clone lookup-index set
    ! <builtins-suspension> builtins store get set-at
    update-local-vars
    check-vars? on
    0 current-index set-global
    H{ } clone rule-firings set
    H{ } clone occurrence-mismatches set
    H{ } clone reactivations set
    H{ } clone var-names set
    H{ } clone guard-fails set
    H{ } clone occurrence-times set
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
    ! [ [ f lift ] map-values ] change-store ;
    [ [ clone [ f lift ] change-constraint ] map-values ] change-store ;

: susp>constraint ( susp -- chr )
    [ constraint>> ] [ ctx>> ] bi
    [ swap C boa ] when* ;
    ! constraint>> ;

: finish-solver-state ( -- state )
    get-solver-state
    petrify-solver-state!
    [ [ susp>constraint ] map-values ] change-store ;

SYMBOL: split-states

: join-states ( assoc -- )
    [ merge-solver-config ] assoc-each ;

: save-split-state ( key solver-state --  )
    2array split-states get push ;

ERROR: chr-inference-error state error cont ;
SYMBOL: chr-query-stats
: last-chr-stats ( -- x ) chr-query-stats get-global ;

: get-rule-name ( rules id -- name )
    swap dupd nth rule-name ;

: rename-rule-firings ( assoc -- assoc )
    program get rules>> swap [ get-rule-name ] with map-keys ;

: score-mismatches ( assoc -- seq )
    [ [ values [ length ] map-sum ] keep 3array ] { } assoc>map
    [ second ] inv-sort-with ;

: show-guard-fails ( assoc -- seq )
    program get rules>> '[ swap first2 [ _ swap get-rule-name ] dip 3array ] { } assoc>map
    [ first ] inv-sort-with ;

: schedule-table ( assoc -- seq )
    program get rules>> swap
    [| rule-num rules result |
     rules rule-num [ get-rule-name ] [ drop f ] if*
     result "run" of [ 0 ] unless*
     result "mismatch" of [ 0 ] unless*
     result "guard" of [ 0 ] unless*
     [ 1000000000 /f ] tri@
     [ + + ] 3keep 5 narray
    ] with { } assoc>map [ second ] inv-sort-with ;

: save-stats ( -- )
    occurrence-times [ get schedule-table ] keep
    lookup-index [ get ] keep
    reactivations [ get ] keep
    rule-firings [ get rename-rule-firings ] keep
    program [ get ] keep
    guard-fails [ get show-guard-fails ] keep
    occurrence-mismatches [ get score-mismatches ] keep associate
    [ set-at ] keep
    [ set-at ] keep
    [ set-at ] keep
    [ set-at ] keep
    [ set-at ] keep
    [ set-at ] keep
    chr-query-stats set-global ;

:: top-time-guzzlers ( table -- table )
    0 :> sum-total! 0 :> total-run! 0 :> total-mismatch! 0 :> total-guard!
    table [| results index |
           results 5 firstn :> ( rule total run mismatch guard )
           sum-total total + sum-total!
           total-run run + total-run!
           total-mismatch mismatch + total-mismatch!
           total-guard guard + total-guard!
           sum-total
    ] map-index
    sum-total 0.9 * [ > ] curry find drop :> cut-index
    table cut-index head-slice
    { "rule" "total" "run" "mismatch" "guard" } prefix
    { "total" sum-total total-run total-mismatch total-guard } suffix
    ;

! WIP
: chr-stats. ( -- )
    last-chr-stats occurrence-times of
    top-time-guzzlers simple-table. ;


: run-chr-query ( prog query -- state )
    [ pred>constraint ] map
    2dup 2array
    [
        H{ } clone context-eqs set
        V{ } clone split-states set
      ! H{ } clone result-config set
      0 state-id set-global
      0 sentinel set
      H{ } clone ground-values set
      swap
      init-chr-scope
      V{ } clone queue set
      f swap activate-new
      ! run-queue
      [ run-queue ] [ dup chr-inference-error? [ rethrow ]
                      [ save-stats get-solver-state swap error-continuation get chr-inference-error ] if ] recover

      ! split-states get join-states
      ! run-queue
      finish-solver-state
      [ save-stats ] when-trace-stats
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
    current-context get
    [ call-next-method ]
    [ 2drop queue off ] if
    ;

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

! ** Dynamic Equivalence
: maybe-add-context-eq ( rhs lhs -- )
    swap dup term-var?
    [ current-context get context-eqs get [ drop H{ } clone ] cache
      set-at ]
    [ 2drop ] if ;

M: Is activate-new
    dup [ var>> ] [ src>> ] bi maybe-add-context-eq
    call-next-method
    ;
! ** Runner

: run-chrat-query ( query -- store )
    prepare-query run-chr-query ;

: query-with ( solver query -- store )
     prepare-query-with run-chr-query ;

ALIAS: == test-eq
ALIAS: ==! make-equal
