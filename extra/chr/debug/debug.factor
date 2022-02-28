USING: accessors arrays assocs assocs.extras chr chr.programs chr.state
formatting io kernel math.parser namespaces prettyprint sequences terms
tools.annotations ;

IN: chr.debug

: chr-state. ( -- )
    store get "Store: " write
    [ constraint>> ] map-values . ;

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
    ! \ activate [ [ chr-state. dup "Activating: %d\n" printf ] prepose ] annotate
    ! \ activate [ [ "! " write dup id-susp. ] prepose ] annotate
    ! \ test-callable [ [ dup "Builtin Test: " write . ] prepose [ dup " ==> %u\n" printf ] compose ] annotate
    ! \ run-occurrence [ [ dup occurrence>> "Try Occurrence %u with Schedule: " printf dup partners>> . ] prepose ] annotate
    ! \ run-occurrence [ [ 2dup try-rule-match. ] prepose ] annotate
    \ collect-chrat-solvers [ [ "Solvers for Program: " write dup . ] compose ] annotate
    \ load-chr [ [ "Rewritten Program: " write dup rules>> <enumerated> >array . ] compose ] annotate
    ! \ replace-all-equalities [ [ ground-values get "Ground-values: " write . ] prepose ] annotate
    \ make-equal [ [ 2dup "Unify: %u ==! %u\n" printf ] prepose ] annotate
    ;
