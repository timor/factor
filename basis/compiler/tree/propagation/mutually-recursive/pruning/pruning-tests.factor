USING: compiler.tree compiler.tree.propagation.mutually-recursive.pruning
compiler.tree.propagation.mutually-recursive.tests kernel tools.test ;
IN: compiler.tree.propagation.mutually-recursive.pruning.tests

FROM: compiler.tree.propagation.branches => live-branches ;

{ { t f } t } [ test-call test-if branch-with-call? ] unit-test
{ f f } [ test-call node new branch-with-call? ] unit-test

! { { f f } f } [ test-call test-if { t f } swap >#recursion-branch branch-with-call? ] unit-test
{ { t f } t } [ test-call test-if branch-with-call? ] unit-test

! { f f } [ test-call node new convert-recursive-branch drop test-call swap branch-with-call? ] unit-test
! { { f f } f } [ test-call test-if convert-recursive-branch drop test-call swap branch-with-call? ] unit-test
! { { t f } t } [ node new test-if convert-recursive-branch drop test-call swap branch-with-call? ] unit-test

! { t } [ test-call test-tree prune-recursive-call drop [ #recursion-branch? ] contains-node? ] unit-test

! { t f } [ test-call test-tree [ prune-recursive-call swap ] keepd swap prune-recursive-call nip ] unit-test

! Cloning Labels ( obsolete )

! { t f } [ \ (each-integer) <inline-recursive>
!           [ dup clone [ id>> ] bi@ eq? ]
!           [ dup clone-label [ id>> ] bi@ eq? ] bi ] unit-test


! { t } [
!     \ (each-integer) <inline-recursive> { } { } <#recursive>
!     dup clone [ label>> id>> ] bi@ =
! ] unit-test

! { f } [
!     \ (each-integer) <inline-recursive> { } { } <#recursive>
!     dup clone-recursive [ label>> id>> ] bi@ =
! ] unit-test
