USING: accessors arrays assocs assocs.extras chr chr.factor.composition
chr.programs chr.state classes.builtin combinators continuations effects
formatting io kernel math math.parser namespaces prettyprint prettyprint.custom
quotations sequences sequences.extras sets sorting system terms
tools.annotations tools.annotations.private tools.time tools.walker ;

IN: chr.debug
FROM: namespaces => set ;

: solve-builtins ( eq-consts -- subst )
    [ [ lhs>> ] [ rhs>> ] bi 2array ] map solve-problem ;

: solve-result-store ( store -- store )
    dup [
        clone >alist dup builtins swap delete-at* drop
        solve-builtins lift
    ] with-term-vars ;



: store. ( assoc -- )
    sort-keys . ;

: susp-store. ( consts -- )
    [ constraint>> f lift ] map-values
    store. ;

: chr-state. ( -- )
    store get "Store: " write
    store. ;

: solver-state-chrs ( state -- assoc )
    store>>
    [ constraint>> f lift ] map-values sort-keys ;

: pprint-solver-state ( state -- )
    dup builtins>> [
        solver-state-chrs pprint*
        ! store>> pprint*
    ] with-var-context ;

M: solver-state pprint*
    solver-state-chrs pprint* ;

! : chrebug ( -- )
!     \ check/update-history [ [ 2dup "Rule %d match with match trace: %u\n" printf ] prepose ] annotate
!     \ kill-chr [ [ dup "Killing id %d\n" printf  ] prepose ] annotate
!     \ run-rule-body [ [ 2dup [ dup program get rules>> nth ] dip "Running Rule %d: %u\n with substitution:\n %u\n" printf ] prepose ] annotate
!     \ activate-new [ [ dup "Activating new constraint: %u\n" printf ] prepose ] annotate
!     \ activate [ [ chr-state. dup "Activating: %d\n" printf ] prepose ] annotate
!     \ test-callable [ [ dup "Builtin Test: " write . ] prepose [ dup " ==> %u\n" printf ] compose ] annotate
!     \ run-occurrence [ [ dup occurrence>> "Try Occurrence %u with Allowed Vars: " printf dup rule-vars>> . ] prepose ] annotate
!     \ collect-chrat-solvers [ [ "Solvers for Program: " write dup . ] compose ] annotate
!     \ load-chr [ [ "Rewritten Program: " write dup rules>> <enumerated> >array . ] compose ] annotate
!     ;

: rule-id ( id -- id/name )
    [ number>string ] keep program get rules>> nth dup named-chr? [ rule-name>> "(" ")" surround " " glue ] [ drop ] if
    "R" prepend ;
    ! [ drop ] if ;

: rule-match. ( rule-id bindings -- )
    ! 2dup [ rule-id ] dip "Rule Match %s with: %u\n" printf
    over rule-id "Rule Match %s with: " printf
    [ program get rules>> nth clone f >>match-vars f >>existentials ] dip
    lift . flush ;

: susp. ( chr-suspension --  )
    {
        ! [ id>> "%d: " printf ]
        [ id>> "%u: " printf ]
        [ ctx>> [ " (%u) " printf ] when* ]
        [ constraint>> f lift* pprint ]
        [ from-rule>> [ rule-id " (Rule: %s)\n" printf ] [ nl ] if* ]
    }
    cleave flush ;

: id-susp. ( id -- )
    store get at susp. flush ;

: try-rule-match. ( c schedule -- )
    swap id>> "Try id %d on Rule: " printf occurrence>> first rule-id . flush ;

SYMBOL: rule-matches

: reset-rule-matches ( -- )
    H{ } clone rule-matches set ;

: remember-rule-match ( id -- )
    rule-matches get inc-at ;

: unused-rules. ( -- )
    "Unused Rules:" print
    program get rules>> <enumerated>
    rule-matches get keys [ in? ] curry reject-keys
    [ ! ( rules id )
        rule-name
    ] { } assoc>map . ;

: rule-match-report. ( -- )
    "Rule Match Stats:" print
    program get rules>> rule-matches get sort-keys
    [ ! ( id rules count  )
        [ [ nth ] keepd swap rule-name ] dip
    ] with assoc-map . ;

SYMBOL: debug-chr-stats

: chr-usage-report. ( -- )
    debug-chr-stats get [ rule-match-report.
    unused-rules. ] when ;

: chrebugabit ( -- )
    \ create-chr [ [ "+ " write dup id-susp. ] compose
                   ! [ chr-state. ] compose
    ] annotate
    ! \ check/update-history [ [ 2dup "Rule %d match with match trace: %u\n" printf ] prepose ] annotate
    \ kill-chr [ [ "- " write dup id-susp. ] prepose ] annotate ;

: chrebug ( -- )
    ! \ check/update-history [ [ 2dup "Rule %d match with match trace: %u\n" printf ] prepose ] annotate
    \ kill-chr [ [ "- " write dup id-susp. ] prepose ] annotate
    \ run-rule-body [ [ 2dup over remember-rule-match rule-match. ] prepose
                      ! [ chr-state. ] prepose ! Very verbose
    ] annotate
    ! \ activate-new [ [ dup "Activating new constraint: %u\n" printf ] prepose ] annotate
    \ create-chr [ [ "+ " write dup id-susp. ] compose
                   ! [ chr-state. ] compose
    ] annotate
    ! \ activate [ [ "! " write dup . ] prepose ] annotate
    ! \ test-callable [ [ dup "Builtin Test: " write . ] prepose [ dup " ==> %u\n" printf ] compose ] annotate
    ! \ run-occurrence [ [ dup occurrence>> "Try Occurrence %u with Schedule: " printf dup partners>> . ] prepose ] annotate
    ! \ run-occurrence [ [ 2dup try-rule-match. ] prepose ] annotate
    \ init-chr-scope [ [ reset-rule-matches ] compose ] annotate
    \ collect-chrat-solvers [ [ "Solvers for Program: " write dup . ] compose ] annotate
    \ load-chr [ [ "Rewritten Program: " write dup rules>> <enumerated> >array . ] compose ] annotate
    ! \ replace-all-equalities [ [ ground-values get "Ground-values: " write . ] prepose ] annotate
    \ make-equal [ [ 2dup "Unify: %u ==! %u\n" printf ] prepose ] annotate
    M\ chr-or activate-new [ [ "SPLIT" print ] prepose ] annotate
    M\ chr-branch activate-new [ [ "BRANCH" print ] prepose [ "RETURN" print ] compose ] annotate
    ! M\ C activate-new [ '[ current-context get _ dip current-context get "CTX %u -> %u\n" printf ] ] annotate
    ! M\ C activate-new [ [ dup ctx>> current-context get swap "CTX: %u -> %u\n" printf ] prepend ] annotate
    \ run-queue [ [ "Flushing queue" print ] prepose ] annotate
    \ merge-solver-config [ [ 2dup swap "Merging store with key: %u\n" printf store>> [ constraint>> ] map-values . ] prepend ] annotate
    \ finish-solver-state [ [ chr-usage-report. ] compose ] annotate
    ;

: debug-rm ( -- )
    \ run-rule-body [ [ 2dup rule-match. ] prepose ] annotate ;

:: break-rule-match ( occ -- )
    \ run-occurrence [ dup occurrence>> occ =  ] breakpoint-if ;

:: break-id-match ( rule-num susp-id -- )
    \ run-occurrence [ 2dup [ id>> susp-id = ] [ occurrence>> first rule-num = ] bi* and ] breakpoint-if ;

! ** Conditional debug stuff
SYMBOL: debug-cond
! : run-with-cond ( quot -- )
!     [ t debug-cond set-global  ] dip
!     [  ] [ f debug-cond set-global ] cleanup ; inline

! : annotate-if ( trigger-word condition target-word annotation -- )
: annotate-trigger ( trigger-word condition -- )
    '[ [ @ [ t debug-cond set-global ] when ] prepose
       '[ _ [ f debug-cond set-global ] finally ]
    ] annotate ;

MACRO: entering-if ( word cond-quot -- quot )
    [ dup stack-effect [ in>> ] "Entering" trace-quot ] dip swap
    '[ @ _ when ] ;

MACRO: leaving-if ( word cond-quot -- quot )
    [ dup stack-effect [ out>> ] "Leaving" trace-quot ] dip swap
    '[ @ _ when ] ;

: (watch-if) ( word cond-quot def -- def )
    2over
    '[ _ _ entering-if @ _ _ leaving-if ] ;

: watch-if ( word cond-quot -- )
    dupd '[ [ _ _ ] dip (watch-if) ] annotate ;

:: trigger-id-match ( rule-num susp-id -- )
    \ run-occurrence [ 2dup [ id>> susp-id = ] [ occurrence>> first rule-num = ] bi* and ] annotate-trigger
    ! M\ C match-constraint [ [ debug-cond get [ break ] when ] prepose ] annotate
    \ match-constraint-in-context [ debug-cond get ] watch-if
    ! \ sort-lookup [ debug-cond get ] watch-if
    \ try-schedule-match [ debug-cond get ] watch-if
    \ check-guards [ debug-cond get ] watch-if
    ! \ activate-item watch
    ! \ reactivate watch
    ;


TUPLE: chr-run
    prog records rule-results activations ;
TUPLE: rule-result
    name count time per-firing ;
SYMBOL: chr-trace
: push-chr-record ( record -- )
    chr-trace get-global records>> push ;

: new-chr-run ( prog -- obj )
    chr-run new swap >>prog
    V{ } clone >>records
    H{ } clone >>rule-results
    ;

: new-rule-result ( name -- obj )
    0 0 0 rule-result boa ;

: trace-activate ( id -- data )
    dup store get at
    [ type>> 2array ]
    [ f 2array ] if*
    \ activate prefix ;

: chriming ( -- )
    \ run-chr-query [ [ over new-chr-run chr-trace set-global ] prepose ] annotate
    \ activate [ [ nano-count over trace-activate 2array push-chr-record ] prepose ] annotate
    \ fire-rule [ [ nano-count reach \ fire-rule swap 2array 2array push-chr-record ] prepose ] annotate
    ;

! { timestamp duration } pairs
: chr-deltas ( chr-run -- seq )
    records>>
    dup first first
    '[ _ - ] map-keys
    unzip swap dup 1 rotate
    [ [ swap - ] keepd swap 2array ] 2map
    swap zip
    ;

:: read-trace-record ( run record -- run )
    record first2 :> ( timing data )
    data first
    { { [ dup \ fire-rule eq? ]
        [ drop timing second :> delta
          data second
          run rule-results>> [ run prog>> nth rule-name>> new-rule-result ] cache
          [ 1 + ] change-count
          [ delta + ] change-time drop
        ] }
      [ drop ]
    } cond
    run ;

<PRIVATE
: calculate-per-firings ( run -- run )
    dup rule-results>> [ nip
        dup [ time>> ] [ count>> ] bi /f >>per-firing
        drop
     ] assoc-each ;

: duration. ( duration -- )
    1000 /f "%10.2f" printf ;

PRIVATE>

: read-chr-trace ( -- run )
    chr-trace get-global
    dup chr-deltas
    [ read-trace-record ] each
    calculate-per-firings
    ;

: rule-result. ( rule-result -- )
    {
        [ count>> "%5d" printf bl ]
        [ time>> duration. bl ]
        [ per-firing>> duration. bl ]
        [ name>> write nl ]
    } cleave ;

: chr-report. ( -- )
    read-chr-trace
    rule-results>> values [ time>> ] inv-sort-with
    [ rule-result. ] each ;

! GENERIC: <=>* ( obj1 obj2 -- <=> )
! M: object <=>* <=> ;
! M: sequence <=>*
!     [ mismatch ] 2keep pick [ 2nth-unsafe <=>* ] [ [ length ] compare nip ] if ;
! M: tuple <=>* over tuple? [ [ tuple>array ] bi@ ] [ [ class-of class-name ] bi@ ] if <=>* ;

! : c. ( result -- )
!     >alist builtins swap [ at . ] [ pluck-at ] 2bi
!     { { constraint-type <=>* } { constraint-args <=>* } } sort-values-by . ;


: qt. ( quot -- )
    qt sort-keys ... ;

: gt. ( quot -- ) get-type ... ;

: add-chr-timing ( -- )
    {
        try-index-lookup
        lookup-update-index-entry
        add-to-lookup-index
        filter-lookup-context
        ! lookup
        test-callable
      check-guards
      try-schedule-match
      ! resolve-match-context
      check/update-history
      simplify-constraints
    } M\ equiv-activation activate-new suffix
    M\ callable activate-new suffix
    M\ as-pred lookup suffix
    M\ chr-constraint lookup suffix
    M\ chr-sub-pred lookup suffix
    { assume-equal equiv-wakeup-set update-wakeup-set-vars
      update-ground-values!
      maybe-update-ground-values
      check-recursive-terms
      create-chr
      isomorphic?
    } append
    [ add-timing ] each ;

! ** Convenience
: word-timing/total. ( -- )
    word-timing get >alist
    [ second first ] sort-with
    [ first2 first2 [ 1000000000 /f ] dip 2dup /f log10 4array ] map
    dup [ second ] map-sum "Total:" swap "" "" 4array suffix
    simple-table. ;

: time.. ( ..a quot -- ..b )
    reset-word-timing
    time word-timing/total.
    ; inline

: tqt ( quot -- res )
    reset-all
    add-chr-timing
    [ qt ] time.. sort-keys
    reset-all ;
