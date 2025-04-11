USING: continuations kernel namespaces sequences splitting variables ;

IN: choose-fail

! Some backtracking tools
! mostly equivalent to Paul Graham's choose/true-choose

! 22.2

ERROR: no-more-choices ;
ERROR: not-in-choice-context ;
<PRIVATE
VAR: paths
! make sure we actually have a choice stack set
: check ( paths -- paths )
    dup [ not-in-choice-context ] unless ; inline

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

! cf. true-choose
! breadth-first traversal
: bf-choose ( choices -- item )
    [ ! | k choices |
        [ swap [ continue-with ] 2curry ] with map
        [ check append ] change: paths
        fail
    ] curry callcc1 ;
