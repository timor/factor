USING: accessors assocs combinators.short-circuit compiler.crossref
compiler.tree compiler.tree.propagation.info continuations debugger formatting
generic hash-sets io kernel locals math namespaces prettyprint sequences sets
stack-checker.dependencies typed vocabs words ;
IN: compiler.tree.propagation.output-infos

FROM: namespaces => set ;

! Stores the computed output infos of the word currently being compiled
SYMBOL: compiled-output-infos

! * Single Recursive Propagation

! ** Inlining recursive call sites

! Return nodes with all branches removed that contain the call
GENERIC: reject-call* ( call node -- nodes )
M: node reject-call* nip ;
: child-contains-node? ( child node -- ? )
    [ over = ] contains-node?
    nip
    ;

M: #branch reject-call*
    swap over children>> [ child-contains-node? ] with any?
    [ "#branch with call left" throw ] when ;

M: #if reject-call*
    swap over children>> [ child-contains-node? ] with reject
    dup length 2 = [ drop ] [ first nip ] if ;



! * Mutual Recursive Propagation
! Stores the trace of current nested propagation
SYMBOL: nesting-trace

! Stores the trees that have been created during nested compilation, so that
! when the word itself comes up for compilation, the result can be reused.
SYMBOL: nodes-cache


!

! * Old approach: dependencies

TUPLE: depends-on-output-infos word infos ;
! TUPLE: depends-on-method-output-infos word infos ;

! Assoc storing which output infos changed in the current compilation unit
SYMBOL: changed-output-infos

: add-depends-on-output-infos ( word infos -- )
    depends-on-output-infos add-conditional-dependency ;

: explain ( word dep -- )
    [ word>> "output-infos" word-prop ] [ infos>> ] bi
    "%s:\ncurrent infos %[%s, %] differs from stored infos %[%s, %]" printf nl
    ! "Current infos %u differ from dependency infos %u" printf nl
     ;

M: depends-on-output-infos satisfied?
    [ word>> "output-infos" word-prop ] [ infos>> ] bi [ = ] 2all?
    ;


: all-vocab-words ( vocab-spec -- seq )
    vocab-words [ dup subwords swap suffix ] gather ;

GENERIC: get-vocab ( word -- vocab )
M: word get-vocab vocabulary>> ;
M: typed-gensym get-vocab parent-word get-vocab ;
M: method get-vocab parent-word get-vocab ;

! Look into dependency store and filter by vocab, these are the ones that the
! compiler looks at.
: cdeps ( vocab -- assoc )
    compiled-crossref get
    [ drop swap get-vocab = ] with assoc-filter ;


! Unsatisfied dependencies of cross-refs point of view
: ucdeps ( x -- x )
    all-vocab-words outdated-conditional-usages
    assoc-combine
    ;

: ucdeps. ( vocab -- )
    ucdeps . ;

! Look which dependencies exist on each word in a vocab
: rdeps ( vocab -- assoc )
    all-vocab-words
    [ dup +conditional+ dependencies-of ] map>alist ;

! List which output-infos each vocab word depends on
: odeps ( vocab -- assoc )
    all-vocab-words [ dup "dependency-checks" word-prop [ depends-on-output-infos? ] filter ]
    map>alist harvest-values ;

! Show unsatisfied dependencies in forward direction
: uodeps ( vocab -- alist )
    odeps [ [ satisfied? ] reject ] assoc-map harvest-values
    ;

: uodeps. ( vocab -- )
    uodeps [ [ explain nl ] with each ] assoc-each ;

! Get the ones that should be recompiled
: rcdeps ( vocab -- seq )
    uodeps keys [ +conditional+ dependencies-of ] map assoc-combine
    keys ;

: should-store-output-infos? ( nodes -- infos/f )
    ! 2 tail* first2              ! last2
    [
        { [ length 2 > ] [ but-last last ] } 1&&
        #terminate? not
    ]
    [ last dup #return?
      [ "STRANGE: last node not return, not storing outputs" print ] unless
      node-input-infos
    ]
    bi and ;


: set-pending-output-infos ( nodes -- nodes )
    ! TODO: check here if interim infos match with finals
    ! dup "output-infos" word-prop [ duplicate-output-infos ] when*
    ! dup "output-infos" word-prop [ "WARNING: overriding output infos: %[%s, %]" printf nl ] when*
    dup should-store-output-infos?
    [
        [ ] [
            [ clone f >>literal? ] map ! This line prevents only literal value propagation
            ! replace-literal-infos      ! This line prevents literal value info propagation completely
            compiled-output-infos set
        ] if-empty
    ] [
    ] if* ;

: changed-output-infos? ( word -- infos/f )
    dup "output-infos" word-prop compiled-output-infos get
    2dup =
    [ 3drop f ]
    [
        ! [ "output infos of %s changed: %[%s, %] -> %[%s, %]" printf nl ]
        [ nip swap changed-output-infos get set-at ]
        [ 2nip ] 3bi
    ]
    if ;

! Update output infos of word with current infos.
: update-output-infos ( word -- )
    ! dup "Check update output-infos: %s" printf nl
    dup changed-output-infos?
    [ [ "output-infos" set-word-prop ] [
          ! Does not work as intended from within the unit
          ! changed-conditionally
          drop
      ] bi ]
    [ drop ] if* ;

! * Sorting according to deps obsolete

:: all-output-info-dependencies ( vocab -- assoc )
    vocab odeps [ [ word>> ] map [ get-vocab vocab = ] filter ] assoc-map
    harvest-values ;

:: to-recompile-graph ( seq -- assoc )
    seq [
        dup
        [ "dependencies" word-prop ] keep
        "dependency-checks" word-prop [ depends-on-output-infos? ] filter
        [ word>> ] map union
    ] map>alist ;

ERROR: topological-sort-cycle key trace ;
SYMBOL: cycle-set
SYMBOL: current-graph

: not-in-cycle? ( key -- ? )
    dup cycle-set get in? [ cycle-set get topological-sort-cycle ] when ;

: in-unvisited-set? ( unvisited key -- ? ) swap in? ;
: unvisited? ( unvisited key -- ? ) [ in-unvisited-set? ] [ not-in-cycle? ] bi and ;
: visited ( unvisited key -- ) [ swap delete ] [ cycle-set get delete ] bi ;

DEFER: (topological-dep-sort)
: visit-children ( seq unvisited key -- seq unvisited )
    dup cycle-set get adjoin
    current-graph get at [ (topological-dep-sort) ] each ;

: (topological-dep-sort) ( seq unvisited key -- seq unvisited )
    2dup unvisited? [
        [ visit-children ] keep 2dup visited pick push
    ] [
        drop
    ] if ;

: topological-dep-sort ( words -- seq )
    HS{ } clone cycle-set [
        [ V{ } clone ] dip [ clone >hash-set ] keep
        [ (topological-dep-sort) ] each drop
    ] with-variable ;

ERROR: dependency-sort-mismatch diff ;

: sort-deps ( seq -- seq )
    [
        [ topological-dep-sort ] keep over
        diff dup null? [ drop ] [ dependency-sort-mismatch ] if
    ] [ dup topological-sort-cycle? [ error. ] [ rethrow ] if ] recover
    ;

: sort-output-infos ( graph -- seq )
    [ keys ] keep current-graph [
        sort-deps
    ] with-variable ;


! [ sort-to-recompile ]
! [ dup topological-sort-cycle? [ error. ] [ rethrow ] when ] recover
: sort-to-recompile ( seq -- seq )
    [ to-recompile-graph sort-output-infos ]
    [ dup topological-sort-cycle? [ error. ] [ rethrow ] if ] recover
    ;

! : sort-to-recompile ( seq -- seq )
!     [ (sort-to-recompile) ] keep
!     2dup [ = ] 2all?
!     [ drop ]
!     [ dupd swap "sorting produced difference:" print . . ] if ;

! Recompile vocab until all output infos have been propagated
: reload-aggressive ( vocab -- )
    dup reload
    [ dup uodeps empty? not dup [ over length "Unsatisfied: %s, recompiling." printf nl ] when ]
    [
        dup all-vocab-words sort-to-recompile recompile drop ] while
    drop ;
