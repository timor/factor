USING: accessors assocs combinators.short-circuit compiler.tree.builder
compiler.tree.propagation compiler.tree.propagation.info
compiler.tree.propagation.inlining kernel math sequences tools.test vocabs words
;
IN: compiler.tree.propagation.inlining.tests

: inline-info-caches ( words -- assoc )
    [ dup word-inline-infos-cache ] map>alist
    [ nip assoc-empty? ] assoc-reject ;

: clear-inline-info-caches ( -- )
    all-words [ [ "inline-propagation-infos" remove-word-prop ]
                [ "inline-body" remove-word-prop ] bi
    ] each ;

: non-trivial-cache? ( assoc -- ? ) [ nip { [ +inline-recursion+? ] [ { [ empty? not ] [ [ object-info = ] all? not ] } 1&& ] } 1|| ] assoc-any? ;

: non-trivial-inline-info-caches ( words -- assoc )
    inline-info-caches [ nip non-trivial-cache? ] assoc-filter ;

: inline-info-cache-overhead ( -- bytes )
    0
    all-words [
        [ "inline-body" word-prop [ size + ] when* ]
        [ "inline-propagation-infos" word-prop [ size + ] when* ] bi
    ] each ;

{ t } [
    [ >bignum 10 mod ] build-tree propagate
    fourth dup word>> do-inlining
] unit-test

! never-inline-word?
{ t } [
    \ + props>> "default-method" of  never-inline-word?
] unit-test
