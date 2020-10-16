USING: accessors arrays assocs combinators.short-circuit compiler.test
compiler.tree compiler.tree.builder compiler.tree.debugger
compiler.tree.optimizer compiler.tree.propagation.copy
compiler.tree.propagation.info compiler.tree.propagation.inline-propagation
compiler.tree.propagation.simple compiler.units io.encodings.utf8 io.files
kernel literals math memory namespaces prettyprint sequences sorting tools.test
vectors vocabs words ;
IN: compiler.tree.propagation.inline-propagation.tests

! * Interactive Helpers
! : inline-info-caches ( words -- assoc )
!     [ dup word-inline-infos-cache ] map>alist
!     [ nip assoc-empty? ] assoc-reject ;

! : clear-inline-info-caches ( -- )
!     all-words [ reset-inline-info-cache ] each ;

! : non-trivial-cache? ( assoc -- ? ) [ nip { [ +inline-recursion+? ] [ { [ empty? not ] [ trivial-infos? not ] } 1&& ] } 1|| ] assoc-any? ;

! : null-info-cache? ( assoc -- ? ) [ [ [ null-class? ] any? ]
!                                     [ [ class>> null-class? ] any? ] bi* or ] assoc-any? ;

! : literal-info-cache? ( assoc -- ? ) [ nip [ literal?>> ] any? ] assoc-any? ;

! : non-trivial-inline-info-caches ( words -- assoc )
!     inline-info-caches [ nip non-trivial-cache? ] assoc-filter ;

! : inline-info-cache-overhead ( -- bytes )
!     0
!     all-words [
!         [ "inline-body" word-prop [ size + ] when* ]
!         [ "inline-propagation-infos" word-prop [ size + ] when* ] bi
!     ] each ;

! : write-infos ( path -- )
!     all-words non-trivial-inline-info-caches sort-keys swap utf8 [ ... ] with-file-writer ;

! * Unit tests
: swap-only ( x x -- x x ) swap ;
: swap-foldable ( x x -- x x ) swap ; foldable

: swap-user ( x x -- x x ) swap-only ;

{ \ t } [ [ 1 2 swap-only + integer? ] build-tree optimize-tree nodes>quot last ] unit-test
{ \ t } [ [ 1 2 swap-user + integer? ] build-tree optimize-tree nodes>quot last ] unit-test

{ [ \ t ] } [ [ 1 2 swap-foldable + integer? ] build-tree optimize-tree nodes>quot ] unit-test

! Check word dependencies
TUPLE: foo { a integer } ;
GENERIC: frob ( x -- x )
GENERIC: hobble ( x -- x )
M: foo frob a>> 1 + ;
M: foo hobble [ 2 * ] change-a ;
TUPLE: bar < foo ;
M: bar frob a>> number>string ;

: make-something ( -- x ) 47 bar boa ;
: do-something ( -- x ) make-something hobble frob ;

{ string } [ \ do-something final-classes first ] unit-test
