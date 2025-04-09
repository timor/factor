USING: continuations kernel namespaces sequences splitting variables ;

IN: choose-fail

! Some backtracking tools
! Goal: equivalent to Paul Graham's choose/true-choose

! 22.2

ERROR: no-more-choices ;
<PRIVATE
VAR: paths

: push-path ( thing -- )
    paths swap suffix set: paths ;

: pop-path ( -- thing )
    paths unclip-last swap set: paths ;
PRIVATE>

: cut-all ( -- )
    f set: paths ;

: with-choice ( quot -- )
    { } \ paths rot with-variable ; inline

! : fail ( -- * )
!     paths [ no-more-choices ]
!     [ unclip-last swap set: paths call( -- * ) ] if-empty ;
: fail ( -- * )
    paths [ no-more-choices ]
    [ unclip-last swap set: paths call( -- * ) ] if-empty ;

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
    [ fail ] when-empty
    dup length 1 =
    [ first ] [
        unclip-slice
        [| k rest-choices head-choice |
         [ rest-choices choose k continue-with ] push-path
         head-choice
        ] 2curry callcc1
    ] if ;

! 22.5

: mark ( -- )
    [ fail ] push-path ;

: cut-choice ( -- )
    paths { [ fail ] } split1-last dup [ drop ] [ nip ] if
    set: paths ;

! 22.6

! cf. true-choose
! Why in the world does this work???
: bf-choose ( choices -- item )
    [ ! | k choices |
        [ swap [ continue-with ] 2curry ] with map
        paths append set: paths
        fail
    ] curry callcc1 ;
