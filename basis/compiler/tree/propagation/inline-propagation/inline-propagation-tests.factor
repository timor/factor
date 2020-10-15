USING: accessors arrays assocs combinators.short-circuit compiler.test
compiler.tree compiler.tree.builder compiler.tree.debugger
compiler.tree.optimizer compiler.tree.propagation.copy
compiler.tree.propagation.info compiler.tree.propagation.inline-propagation
compiler.tree.propagation.simple compiler.units io.encodings.utf8 io.files
kernel literals math memory namespaces prettyprint sequences sorting tools.test
vectors vocabs words ;
IN: compiler.tree.propagation.inline-propagation.tests

! * Interactive Helpers
: inline-info-caches ( words -- assoc )
    [ dup word-inline-infos-cache ] map>alist
    [ nip assoc-empty? ] assoc-reject ;

: clear-inline-info-caches ( -- )
    all-words [ reset-inline-info-cache ] each ;

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

: write-infos ( path -- )
    all-words non-trivial-inline-info-caches sort-keys swap utf8 [ ... ] with-file-writer ;

! * Unit tests
: swap-only ( x x -- x x ) swap ;
: swap-foldable ( x x -- x x ) swap ; foldable

{ \ t } [ [ 1 2 swap-only + integer? ] build-tree optimize-tree nodes>quot last ] unit-test

{ [ \ t ] } [ [ 1 2 swap-foldable + integer? ] build-tree optimize-tree nodes>quot ] unit-test
DEFER: slice-tail
{ } [ \ slice-tail reset-word ] unit-test

: slice-tail ( -- seq ) 0 9 10 <iota> >vector <slice> 5 tail ;

{ t } [ \ slice-tail word-inline-infos-cache assoc-empty? ] unit-test

: slice-tail-test ( -- seq ) slice-tail ;

{ object } [ \ slice-tail-test final-classes first ] unit-test

{ f } [ \ slice-tail word-inline-infos-cache assoc-empty? ] unit-test

{ t } [ { slice-tail } compile \ slice-tail word-inline-infos-cache assoc-empty? ] unit-test

: john-doe ( x -- x x ) dup ;

{ } [ \ john-doe H{ { { fixnum } f } } "inline-propagation-infos" set-word-prop ] unit-test

{ f ${ object-info object-info }  } [
    value-infos H{ } clone 1array set
    copies H{ } clone set
    47 <literal-info> 11 set-value-info
    [ { 11 } { 22 33 } \ john-doe <#call>
      dup word>> [ cached-inline-propagation-infos ]
      [ output-value-infos >array ] 2bi
       ] with-scope
] unit-test

: john-doe-user ( -- ) 47 john-doe 2drop ;
{  } [ \ john-doe reset-inline-info-cache { john-doe-user } compile ] unit-test

${ fixnum <class-info> dup 2array dup } [
    value-infos H{ } clone 1array set
    copies H{ } clone set
    47 <literal-info> 11 set-value-info
    [ { 11 } { 22 33 } \ john-doe <#call>
      dup word>> [ cached-inline-propagation-infos ]
      [ output-value-infos >array ] 2bi
    ] with-scope
] unit-test
