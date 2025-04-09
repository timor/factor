USING: arrays continuations kernel sequences variables ;

IN: choose-fail


! Some backtracking tools
! Goal: equivalent to Paul Graham's choose/true-choose

! 22.4

! NOTE: forcing delimiting here for now?

ERROR: not-in-choice-context ;
ERROR: no-more-choices ;
<PRIVATE
VAR: paths

: ensure-paths ( -- paths )
    ! paths dup array? [ not-in-choice-context ] unless ;
    paths ;

: push-path ( thing -- )
    ensure-paths swap suffix set: paths ;

: pop-path ( -- thing )
    ensure-paths unclip-last swap set: paths ;
PRIVATE>

SYMBOL: failsym

: cut-all ( -- )
    f set: paths ;

: with-choice ( quot -- )
    { } \ paths rot with-variable ; inline

: fail ( -- x )
    ! ensure-paths [ failsym ]
    paths [ failsym ]
    [ unclip-last swap set: paths call( -- x ) ] if-empty ;

! First try: doesn't work
! : choose ( seq -- item )
!     [ fail ] [
!         unclip swap
!         '[ [ _ choose ] paths push ] callcc0
!     ] if-empty ;

! Hunch: doing the recurrence in the recovery quotation to ifcc amounts to bfs? no...
! Also wrong effects:
! : choose ( seq -- item )
!     [ fail ] [
!         unclip swap ! first rest
!         [ paths push ]
!         [ choose ] bi-curry* ifcc
!     ] if-empty ;

! Does this do dfs or bfs? Also, does it actually use the stack with more than
! one element?
! This one stack-checks

: choose ( seq -- item )
    [ fail ] [
        unclip-slice
        [| k rest-choices head-choice |
         [ rest-choices choose k continue-with ] push-path
         head-choice
        ] 2curry callcc1
    ] if-empty ;

: mark ( -- )
    \ fail push-path ;
