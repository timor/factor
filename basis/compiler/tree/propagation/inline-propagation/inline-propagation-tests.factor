USING: accessors alien.parser arrays assocs benchmark classes classes.algebra
combinators.short-circuit compiler.crossref compiler.test compiler.tree.builder
compiler.tree.combinators compiler.tree.debugger compiler.tree.optimizer
compiler.tree.propagation.inline-propagation.cache compiler.units continuations
effects fry kernel kernel.private locals math math.order math.parser.private
namespaces prettyprint sequences sets stack-checker.dependencies strings
tools.test vectors vocabs vocabs.loader words ;
IN: compiler.tree.propagation.inline-propagation.tests
FROM: namespaces => set ;

! * Interactive Helpers
: final-info' ( word/quot -- seq )
    [ H{ } clone inline-info-cache set
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
    [ optimized ] with-inline-info-cache ;

: optimized'. ( word/quot -- )
    optimized' nodes>quot . ;

: final-classes' ( word/quot -- seq )
    [ final-classes ] with-inline-info-cache ;

: 1or-error ( quot: ( x -- x ) -- x/error )
    [ with-scope ] curry [ nip ] recover ; inline

: final-node-count ( word/quot -- n )
    0 swap
    optimized [ drop 1 + ] each-node ;

: final-node-count' ( word/quot -- n )
    [ final-node-count ] with-inline-info-cache ;

: all-subwords ( words -- words )
    [ [ subwords ] keep prefix ] map concat ;

! Perform propagation with and without inline-propagation
: opt-classes ( words -- assoc )
    [ dup [ [ final-classes ] 1or-error ] [ [ final-classes' ] 1or-error ] bi 2array
    ]  H{ } map>assoc  ;

! Perform above, but with a shared inline-info cache
: opt-classes' ( words -- assoc )
    [ [ dup [ [ H{ { inline-info-cache f } { inline-propagation f } } [ final-classes ] with-variables ] 1or-error ] [ [ final-classes' ] 1or-error ] bi 2array
    ]  H{ } map>assoc ] with-inline-info-cache ;
    ! t inline-propagation [ [ opt-classes ] with-inline-info-cache ] with-variable ;

: check-classes ( words -- assoc )
    all-subwords opt-classes' [ nip first2 = ] assoc-reject ;

! Compare whether it makes a difference if we share an inline-cache inside a unit or not
: opt-scoped ( words -- assoc1 assoc2 )
    all-subwords [ opt-classes' ] [ opt-classes ] bi ;

: opt-quots ( words -- assoc )
    all-subwords [ dup [ [ optimized nodes>quot ] 1or-error ] [ [ optimized' nodes>quot ] 1or-error ] bi 2array ] H{ } map>assoc ;

: check-quots ( words -- assoc )
    opt-quots [ nip first2 [ quot= ] [ 3drop f ] recover ] assoc-reject ;

: final-deps ( word/quot -- assoc )
    [
        H{ } clone dependencies namespaces:set
        H{ } clone generic-dependencies namespaces:set
        HS{ } clone conditional-dependencies namespaces:set
        optimized drop
        get-dependencies-namespace
    ] with-scope ;

: final-deps' ( word/quot -- assoc ) [ final-deps ] with-inline-info-cache ;

: opt-deps ( words -- assoc )
    [ dup [ [ final-deps ] 1or-error ] [ [ final-deps' ] 1or-error ] bi 2array
    ]  H{ } map>assoc  ;

: check-deps ( words -- assoc )
    opt-deps [ nip first2 = ] assoc-reject ;

: deps-diff ( opt-deps -- assoc )
    [ first2 [
          [ conditional-dependencies get cardinality
            generic-dependencies get assoc-size
            dependencies get values [ +definition+ = ] count
            3array
          ] with-variables
      ] bi@ [ swap - ] 2map ] assoc-map ;

: diff-deps ( words -- assoc )
    check-deps deps-diff ;

: check-vocab-opt ( vocab-name -- res )
    dup ".private" append [ dup require vocab-words all-subwords ] bi@ append
    check-quots ;

: compare-benchmark ( vocab -- res )
    [ dup reload run-timing-benchmark ] [ [ dup reload ] with-inline-info-cache run-timing-benchmark ] bi
    2array ;

! recompile set of words with shared inline-cache, record entries in assoc of alists
: collect-inline-cache ( assoc words -- assoc )
    [ recompile drop inline-info-cache get [| word cache | cache [ 2array word pick push-at ] assoc-each ] assoc-each ] with-inline-info-cache ;

! ! Check how inline-info-cache scope affects the output classes of words
! : check-cache-independence ( words -- res )
!     all-subwords
!     [ [ "--- Individual" nl print flush [ dup . flush dup [ final-classes' ] 1or-error ] H{ } map>assoc ]
!       [ "--- Shared" nl print flush dup invalidate-inline-info [ [ dup . flush dup [ final-classes ] 1or-error ] H{ } map>assoc  ] with-inline-info-cache ] bi  ] keep
!     [| individual shared word | word word individual at word shared at 2array ] 2with H{ } map>assoc
!     ! [ nip first2 = ] assoc-reject
!     ;

: collect-by-signatures ( assoc -- assoc )
    H{ } clone swap [| name pairs | pairs [ first2 :> ( sig entry ) entry name sig 2array pick push-at ] each ] assoc-each ;

: check-inline-cache-consistency ( assoc -- assoc )
    collect-by-signatures [ nip [ classes>> ] map members length 1 = ] assoc-reject ;

: inline-cache-consistent? ( assoc -- ? )
    check-inline-cache-consistency assoc-empty? ;

: inconsistent-classes ( assoc -- assoc )
    check-inline-cache-consistency [ [ classes>> ] map members ] assoc-map ;

ERROR: inconsistent-inline-info-cache cache ;

: check-cache-independence ( words -- cache ? )
    H{ } clone swap [
        1array collect-inline-cache
        ! dup inline-cache-consistent? [ inconsistent-inline-info-cache ] unless
    ] each dup inline-cache-consistent? ;

! Given a sequence of words whose compilation order causes an inconsistency, bisect backwards until the
! start and end of the problem are found
! Find the first index for which the tail sequence returns true
: (bisect-init) ( seq -- seq start current end )
    dup length 1 - [ 1 - ] keep dup ;

: bisect-false ( start current end -- start current end )
    drop [ over - 2 * - 0 max ] 2keep ;
    ! 2dup swap - 2 * swap [ - 0 max ] dip over ;

: bisect-true ( start current end -- start current end )
    [ nipd dupd over - 2 /i + ] keep ;
    ! 2dup swap - 2 /i 1 max - dup ;

! : bisect-continue? ( start current end quot -- start current end quot ? )
!     ! 2drop =
!     reach reach = ;
!     ! 2over = ;
!     ! { [ drop -1 = ] [ = ] } 2|| ;

: bisect-start ( seq quot -- seq start current end quot )
    [ (bisect-init) ] dip ;

: bisect-step ( seq start current end quot -- seq start current end quot ? )
    [ [ reach pick tail-slice ] dip call( slice -- true? )
      [ [ bisect-false ] unless ] keep
      ! [ bisect-true ] [ bisect-false ] if
    ] keep swap ;
    ! [ pick ] 2dip [ tail-slice ] dip [ call( slice -- true? ) ! seq bad-start good-start good?
    !                                    [ bisect-good ] [ bisect-bad ] if ! seq bad-start good-start next-start
    ! ] keep ;

! : bisect-tail ( seq quot: ( slice -- ? ) -- seq start current end ? )
!     bisect-start [ bisect-continue? [  ] [  ]] [ drop [ bisect-false ] dip ] while
!     ! drop swap - 1 <= ;
!     nip ;
! 15190 f
! 14166 f (?)
! 13654 f
! 13398 t
! 13142 t


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

: inline-test ( quot -- quot ) [ with-inline-info-cache ] curry ; inline

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
{ V{ object object } } [ \ scan-function-name final-classes ] inline-test unit-test

{ V{ object } } [ [ { word vector } declare assoc-stack ] final-classes' ] unit-test

! * Understanding inline dependencies

: inlinee-1 ( x x -- x x ) swap swap ; inline
: inlinee-2 ( x x -- x x ) inlinee-1 ; inline
: inliner ( x x -- x x ) inlinee-2 ;
: stupid ( x x -- x x ) swap ;
: callee-1 ( x x -- x x ) stupid swap 1 + ;
: callee-2 ( x x -- x x ) callee-1 ;
: callee-3 ( x x -- x x ) callee-2 ;
: calling ( x x -- x x ) callee-3 ;

! calling should have a n inline dependency on all 3 callees, but not on stupid
! That test does not work, have to check compiled-crossref instead:
! { { +definition+ } } [ \ calling final-deps' dependencies of values members ] unit-test
{ f } [ \ calling final-deps' dependencies of \ stupid of ] unit-test

{ { H{ { generic-dependencies H{ } } { conditional-dependencies HS{ } } { dependencies H{ { + +effect+ } { stupid +effect+ } } } }
    H{ { generic-dependencies H{ } } { conditional-dependencies HS{ } } { dependencies H{ { callee-1 +definition+ } } } }
    H{ { generic-dependencies H{ } } { conditional-dependencies HS{ } } { dependencies H{ { callee-2 +definition+ } { callee-1 +definition+ } } } }
    H{ { generic-dependencies H{ } } { conditional-dependencies HS{ } } { dependencies H{ { callee-1 +definition+ } { callee-2 +definition+ } { callee-3 +definition+ } } } }
    H{ { generic-dependencies H{ } } { conditional-dependencies HS{ } } { dependencies H{ } } }
 } } [ { callee-1 callee-2 callee-3 calling stupid } [ final-deps ] map ] inline-test unit-test

: self-caller ( x -- x ) dup 5 > [ 1 - ] [ self-caller ] if ;
: self-caller-caller ( x -- x ) self-caller ;
: self-caller-caller' ( x -- x ) self-caller-caller ;

{ { H{ { generic-dependencies H{ } } { conditional-dependencies HS{ } } { dependencies H{ { self-caller +effect+ } { if +effect+ } { > +effect+ } { - +effect+ } } } }
    H{ { generic-dependencies H{ } } { conditional-dependencies HS{ } } { dependencies H{ { self-caller +effect+ } } } }
    H{ { generic-dependencies H{ } } { conditional-dependencies HS{ } } { dependencies H{ { self-caller-caller +effect+ } } } }
  } } [ { self-caller self-caller-caller self-caller-caller' } [ final-deps ] map ] inline-test unit-test

! * Dispatch inlining

GENERIC: first-half ( seq -- seq )
M: sequence first-half dup length 2 /i head-slice ;
M: slice first-half [ from>> ] [ to>> ] [ seq>> ] tri
    [ over over - 2 /i + ] dip slice boa ;
PREDICATE: 1box < array length 1 = ;
M: 1box first-half drop f ;
