USING: accessors alien.parser arrays assocs classes classes.algebra
combinators.short-circuit compiler.crossref compiler.test compiler.tree.builder
compiler.tree.debugger compiler.tree.optimizer
compiler.tree.propagation.inline-propagation.cache continuations effects fry
kernel math math.parser.private namespaces sequences strings tools.test vocabs
words ;
IN: compiler.tree.propagation.inline-propagation.tests

! * Interactive Helpers
: final-info' ( word/quot -- seq )
    [
        H{ } clone inline-info-cache set
        final-info ] with-scope ;

: bad-deps ( -- deps )
    all-words dup [ subwords ] map concat append
    H{ } clone tuck '[ _ dependencies-satisfied? ] reject drop [ nip ] assoc-reject keys ;

GENERIC: quot= ( x x -- ? )
M: object quot= = ;
M: f quot= = ;
: same-class? ( obj obj -- ? ) [ class-of ] bi@ class= ;
M: sequence quot=
    2dup same-class?
    [ { [ [ length ] bi@ = ] [ [ quot= ] 2all? ] } 2&& ]
    [ 2drop f ] if ;
PREDICATE: gensym-word < word { [ vocabulary>> not ] [ name>> "( gensym )" = ] } 1&& ;
M: gensym-word quot= swap gensym-word? [ t ] [ f ] if nip ;
M: effect quot= over effect? [ effect= ] [ 2drop f ] if ;
M: shuffle-node quot= over shuffle-node? [ [ effect>> ] bi@ quot= ] [ 2drop f ] if ;
M: wrapper quot= over wrapper? [ [ wrapped>> ] bi@ quot= ] [ 2drop f ] if ;

: optimized ( word/quot -- nodes )
    [ build-tree optimize-tree ] with-scope ;

: optimized' ( word/quot -- nodes )
    [ optimized ] with-inline-propagation ;

: final-classes' ( word/quot -- seq )
    [ final-classes ] with-inline-propagation ;

: 1or-error ( quot: ( x -- x ) -- x/error )
    [ with-scope ] curry [ nip ] recover ; inline

: all-subwords ( words -- words )
    [ [ subwords ] keep prefix ] map concat ;

! Perform propagation with and without inline-propagation
: opt-classes ( words -- assoc )
    [ dup [ [ final-classes ] 1or-error ] [ [ final-classes' ] 1or-error ] bi 2array
    ]  H{ } map>assoc  ;

! Perform above, but with a shared inline-info cache
: opt-classes' ( words -- assoc )
    [ opt-classes ] with-inline-info-cache ;

: check-classes ( words -- assoc )
    all-subwords opt-classes' [ nip first2 = ] assoc-reject ;

! Compare whether it makes a difference if we share an inline-cache inside a unit or not
: opt-scoped ( words -- assoc1 assoc2 )
    all-subwords [ opt-classes' ] [ opt-classes ] bi ;

: opt-quots ( words -- assoc )
    all-subwords [ dup [ [ optimized nodes>quot ] 1or-error ] [ [ optimized' nodes>quot ] 1or-error ] bi 2array ] H{ } map>assoc ;

: check-quots ( words -- assoc )
    opt-quots [ nip first2 quot= ] assoc-reject ;

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

: inline-test ( quot -- quot ) [ with-inline-propagation ] curry ;

{ \ t } [ [ 1 2 swap-only + integer? ] build-tree optimize-tree nodes>quot last ] inline-test unit-test
{ \ t } [ [ 1 2 swap-user + integer? ] build-tree optimize-tree nodes>quot last ] inline-test unit-test

{ [ \ t ] } [ [ 1 2 swap-foldable + integer? ] build-tree optimize-tree nodes>quot ] inline-test unit-test

! Check word dependencies
TUPLE: foo { a integer } ;
GENERIC: frob ( x -- x )
GENERIC: hobble ( x -- x )
M: foo frob a>> 1 + ;
M: foo hobble [ 2 * ] change-a ;
TUPLE: bar < foo ;
M: bar frob a>> 10 (positive>base) ;

: make-something ( -- x ) 47 bar boa ;
: do-something ( -- x ) make-something hobble frob ;

{ string } [ \ do-something final-classes first ] inline-test unit-test

! Inlining with repeating slot signature structure results in retain stack overflow
{ object } [ \ scan-function-name final-classes first ] inline-test unit-test
