USING: continuations kernel namespaces sequences splitting variables ;

IN: choose-fail

! Some backtracking tools
! mostly equivalent to Paul Graham's choose/true-choose

! 22.2

ERROR: no-more-choices ;
ERROR: not-in-choice-context ;
<PRIVATE
VAR: paths

! paths: stack model: next to take is at the end
! choose as dfs: fail invokes last continuation, re-pushes its next choice as
! new last
! bf-choose as bfs: all continuations are prepended, fail invokes successively from tail
! make sure we actually have a choice stack set
: check ( paths -- paths )
    ! dup [ not-in-choice-context ] unless ; inline
    ;

: push-path ( cont -- )
    [ check swap suffix ] change: paths ;

: pop-path ( -- cont )
    [ check unclip-last swap ] change: paths ;

PRIVATE>

: cut-all ( -- )
    f set: paths ;

: with-choice ( quot -- )
    { } \ paths rot with-variable ; inline

: choosing ( quot -- quot )
    [ with-choice ] curry ; inline

: fail ( -- * )
    paths check [ no-more-choices ]
    [ unclip-last swap set: paths call( -- * ) ] if-empty ;

! depth-first traversal
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
    [ check { [ fail ] } split1-last dup [ drop ] [ nip ] if ]
    change: paths ;

! 22.6

! this construct does some kind of control inversion:
! [| k | [| k2 | k2 v set 1 . 2 . k continue ] callcc0 3 . 4 . ] callcc0
! IN: scratchpad auto-use [| k | [| k2 | k2 v set 1 . 2 . k continue ] callcc0 3 . 4 . ] callcc0
! 1
! 2
! IN: scratchpad auto-use v get continue
! 3
! 4
! IN: scratchpad auto-use 


! This is an expansion of { 1 2 3 } amb-unsafe
! [| |
!     1 failure get :> fail-val-1
!     [| k0 |
!      [| k3 | k3 failure set k0 continue ]
!      callcc0
!      fail-val-1 failure set
!      drop 2 failure get :> fail-val-2
!      [| k1 |
!       [| k2 | k2 failure set k1 continue ]
!       callcc0
!       fail-val-2 failure set
!       drop 3 ]
!      callcc0
!     ] callcc0
! ]

! cf. true-choose
! breadth-first traversal
! naive bfs from dfs: just prepend next instead of appending?
! -> nope: only changes search order? still loops, though
! : bf-choose ( seq -- item )
!     [ fail ] when-empty
!     dup length 1 =
!     [ first ] [
!         unclip-slice
!         [| k rest-choices head-choice |
!          [ rest-choices bf-choose k continue-with ]
!          [ check swap prefix ] change: paths
!          head-choice
!         ] 2curry callcc1
!     ] if ;

! NOTE: this one appends all continuations, even the untaken ones.
: bf-choose ( choices -- item )
    [ ! | k choices |
        ! <reversed>
        [ swap [ continue-with ] 2curry ] with map
        [ check append ] change: paths
        fail
    ] curry callcc1 ;


: when-failing ( try-quot recover-quot -- quot )
    '[ _ [ dup no-more-choices? [ drop @ ] [ rethrow ] if ] recover ] ; inline


! : either ( quot1 quot2 -- )
!     [
!         [
!             [ (get-catchstack) push ] dip call
!             (get-catchstack) pop*
!         ] curry
!     ] dip ifcc
