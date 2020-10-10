USING: accessors assocs combinators.short-circuit compiler.tree.propagation.info
compiler.tree.propagation.inline-propagation kernel math memory sequences vocabs
words ;
IN: compiler.tree.propagation.inline-propagation.tests

! * Interactive Helpers
: inline-info-caches ( words -- assoc )
    [ dup word-inline-infos-cache ] map>alist
    [ nip assoc-empty? ] assoc-reject ;

: clear-inline-cache ( word -- )
    [ subwords ] keep suffix
    [ [ "inline-propagation-infos" remove-word-prop ]
      [ "inline-body" remove-word-prop ] bi ] each  ;

: clear-inline-info-caches ( -- )
    all-words [ clear-inline-cache ] each ;

: non-trivial-cache? ( assoc -- ? ) [ nip { [ +inline-recursion+? ] [ { [ empty? not ] [ trivial-infos? not ] } 1&& ] } 1|| ] assoc-any? ;

: null-info-cache? ( assoc -- ? ) [ [ [ null-class? ] any? ]
                                    [ [ class>> null-class? ] any? ] bi* or ] assoc-any? ;

: literal-info-cache? ( assoc -- ? ) [ nip [ literal?>> ] any? ] assoc-any? ;

: non-trivial-inline-info-caches ( words -- assoc )
    inline-info-caches [ nip non-trivial-cache? ] assoc-filter ;

: inline-info-cache-overhead ( -- bytes )
    0
    all-words [
        [ "inline-body" word-prop [ size + ] when* ]
        [ "inline-propagation-infos" word-prop [ size + ] when* ] bi
    ] each ;

! * Unit tests
: swap-only ( x x -- x x ) swap ;
: swap-foldable ( x x -- x x ) swap ; foldable

{ \ t } [ [ 1 2 swap-only + integer? ] build-tree optimize-tree nodes>quot last ] unit-test

{ [ \ t ] } [ [ 1 2 swap-foldable + integer? ] build-tree optimize-tree nodes>quot ] unit-test
