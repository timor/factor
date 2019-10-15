USING: accessors assocs kernel math.vectors namespaces sequences vectors ;
IN: compiler.tree.propagation.mutually-recursive.branch-overrides


! Keep track of branches which should not be propagated when inlining call
! bodies for (mutually) recursive word propagation

! Assoc stack, associating the branch conditions with child branches that should
! be considered dead
SYMBOL: branch-overrides

: init-branch-overrides ( -- ) H{ } clone 1vector branch-overrides set ;

: enter-branch-overrides-scope ( -- )
    branch-overrides get [ last clone ] [ push ] bi ;

: exit-branch-overrides-scope ( -- )
    branch-overrides get pop drop ;

:: with-branch-overrides ( quot -- )
    enter-branch-overrides-scope
    quot call
    exit-branch-overrides-scope ; inline

! Access by values
: (get-branch-overrides) ( in-d -- flags )
    branch-overrides get assoc-stack ;

: (add-branch-overrides) ( in-d flags -- )
    [ swap (get-branch-overrides)  [ vor ] when* ] keepd
    branch-overrides get last set-at ;

! Access by #branch
: add-branch-overrides ( flags branch -- )
    in-d>> swap (add-branch-overrides) ;

: get-branch-overrides ( branch -- flags )
    in-d>> (get-branch-overrides) ;

! Given a set of flags, representing e.g. live child branches,
! apply the currently stored override mask, in a negative manner, i.e. a t entry
! will force the corresponding flag to f
: override-children ( flags #branch -- flags' )
    get-branch-overrides [ swap vandn ] when* ;
