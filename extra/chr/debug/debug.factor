USING: accessors arrays assocs assocs.extras chr chr.programs chr.state
classes.builtin formatting io kernel math math.parser namespaces prettyprint
sequences system terms tools.annotations tools.walker ;

IN: chr.debug

: solve-builtins ( eq-consts -- subst )
    [ [ lhs>> ] [ rhs>> ] bi 2array ] map solve-problem ;

: solve-result-store ( store -- store )
    dup [
        clone >alist dup builtins swap delete-at* drop
        solve-builtins lift
    ] with-term-vars ;

: store. ( consts -- )
    [ constraint>> ] map-values
    solve-result-store
    . ;

: chr-state. ( -- )
    store get "Store: " write
    store. ;

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
    lift . ;

: susp. ( chr-suspension --  )
    [ id>> "%d: " printf ] [ constraint>> pprint ]
    [ from-rule>> [ rule-id " (Rule: %s)\n" printf ] [ nl ] if* ] tri ;

: id-susp. ( id -- )
    store get at susp. ;

: try-rule-match. ( c schedule -- )
    swap id>> "Try id %d on Rule: " printf occurrence>> first rule-id . ;

: chrebug ( -- )
    ! \ check/update-history [ [ 2dup "Rule %d match with match trace: %u\n" printf ] prepose ] annotate
    \ kill-chr [ [ "- " write dup id-susp. ] prepose ] annotate
    \ run-rule-body [ [ 2dup rule-match. ] prepose ] annotate
    ! \ activate-new [ [ dup "Activating new constraint: %u\n" printf ] prepose ] annotate
    \ create-chr [ [ "+ " write dup id-susp. ] compose
                   ! [ chr-state. ] compose
    ] annotate
    ! \ activate [ [ "! " write dup . ] prepose ] annotate
    ! \ test-callable [ [ dup "Builtin Test: " write . ] prepose [ dup " ==> %u\n" printf ] compose ] annotate
    ! \ run-occurrence [ [ dup occurrence>> "Try Occurrence %u with Schedule: " printf dup partners>> . ] prepose ] annotate
    ! \ run-occurrence [ [ 2dup try-rule-match. ] prepose ] annotate
    \ collect-chrat-solvers [ [ "Solvers for Program: " write dup . ] compose ] annotate
    \ load-chr [ [ "Rewritten Program: " write dup rules>> <enumerated> >array . ] compose ] annotate
    ! \ replace-all-equalities [ [ ground-values get "Ground-values: " write . ] prepose ] annotate
    \ make-equal [ [ 2dup "Unify: %u ==! %u\n" printf ] prepose ] annotate
    M\ chr-or activate-new [ [ "SPLIT" print ] prepose ] annotate
    M\ chr-branch activate-new [ [ "BRANCH" print ] prepose [ "RETURN" print ] compose ] annotate
    \ run-queue [ [ "Flushing queue" print ] prepose ] annotate
    ;

:: break-rule-match ( occ -- )
    \ run-occurrence [ dup occurrence>> occ =  ] breakpoint-if ;

:: break-id-match ( rule-num susp-id -- )
    \ run-occurrence [ 2dup [ id>> susp-id = ] [ occurrence>> first rule-num = ] bi* and ] breakpoint-if ;

SYMBOL: chr-trace

: chriming ( -- )
    \ run-chr-query [ [ V{ } clone chr-trace set-global ] prepose ] annotate
    \ activate [ [ nano-count \ activate pick dup store get at type>> 3array 2array chr-trace get-global push ] prepose ] annotate
    \ fire-rule [ [ nano-count \ fire-rule reach 2array 2array chr-trace get-global push ] prepose ] annotate
    ;

: chr-deltas ( -- seq )
    chr-trace get-global
    dup first first
    '[ _ - ] map-keys
    unzip swap 0 swap [| delta time | time time delta - 2array time swap ] map
    nip swap zip
    ;

! GENERIC: <=>* ( obj1 obj2 -- <=> )
! M: object <=>* <=> ;
! M: sequence <=>*
!     [ mismatch ] 2keep pick [ 2nth-unsafe <=>* ] [ [ length ] compare nip ] if ;
! M: tuple <=>* over tuple? [ [ tuple>array ] bi@ ] [ [ class-of class-name ] bi@ ] if <=>* ;

! : c. ( result -- )
!     >alist builtins swap [ at . ] [ pluck-at ] 2bi
!     { { constraint-type <=>* } { constraint-args <=>* } } sort-values-by . ;
