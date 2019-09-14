! Copyright (C) 2009, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: assocs combinators compiler.units digraphs fry grouping kernel
namespaces sequences sets stack-checker.dependencies words ;
IN: compiler.crossref

SYMBOL: compiled-crossref

compiled-crossref [ H{ } clone ] initialize

SYMBOL: generic-call-site-crossref

generic-call-site-crossref [ H{ } clone ] initialize

: all-dependencies-of ( word -- assoc )
    compiled-crossref get at ;

: dependencies-of ( word dep-type -- assoc )
    [ all-dependencies-of ] dip '[ nip _ dependency>= ] assoc-filter ;

: outdated-definition-usages ( set -- assocs )
    filter-word-defs [ +definition+ dependencies-of ] map ;

: outdated-effect-usages ( set -- assocs )
    filter-word-defs [ all-dependencies-of ] map ;

: dependencies-satisfied? ( word cache -- ? )
    [ "dependency-checks" word-prop ] dip
    '[ _ [ satisfied? ] cache ] all? ;

: outdated-conditional-usages ( set -- assocs )
    members H{ } clone '[
        +conditional+ dependencies-of
        [ drop _ dependencies-satisfied? ] assoc-reject
    ] map ;

: generic-call-sites-of ( word -- assoc )
    generic-call-site-crossref get at ;

: only-xref ( assoc -- assoc' )
    [ drop crossref? ] { } assoc-filter-as ;

: set-generic-call-sites ( word alist -- )
    concat f like "generic-call-sites" set-word-prop ;

: store-dependencies-of-type ( word assoc symbol prop-name -- )
    [ rot '[ nip _ = ] assoc-filter keys ] dip set-word-prop ;

: store-dependencies ( word assoc -- )
    keys "dependencies" set-word-prop ;

: add-xref ( word dependencies crossref -- )
    rot '[
        swap _ [ drop H{ } clone ] cache _ swap set-at
    ] assoc-each ;

: remove-xref ( word dependencies crossref -- )
    '[ _ at delete-at ] with each ;

: (compiled-xref) ( word dependencies generic-dependencies -- )
    compiled-crossref generic-call-site-crossref
    [ get add-xref ] bi-curry@ bi-curry* bi ;

: compiled-xref ( word dependencies generic-dependencies -- )
    [ only-xref ] bi@
    [ nip set-generic-call-sites ]
    [ drop store-dependencies ]
    [ (compiled-xref) ]
    3tri ;

: load-dependencies ( word -- seq )
    "dependencies" word-prop ;

: (compiled-unxref) ( word dependencies variable -- )
    get remove-xref ;

: generic-call-sites ( word -- alist )
    "generic-call-sites" word-prop 2 group ;

: compiled-unxref ( word -- )
    {
        [ dup load-dependencies compiled-crossref (compiled-unxref) ]
        [ dup generic-call-sites generic-call-site-crossref (compiled-unxref) ]
        [ "dependencies" remove-word-prop ]
        [ "generic-call-sites" remove-word-prop ]
    } cleave ;

: delete-compiled-xref ( word -- )
    [ compiled-unxref ]
    [ compiled-crossref get delete-at ]
    [ generic-call-site-crossref get delete-at ]
    tri ;

: set-dependency-checks ( word deps -- )
    members f like "dependency-checks" set-word-prop ;

! * Compute Compilation Order
! Needed to ensure correct output type propagation.  Add stuff in DFS order.

! SYMBOL: candidates

: effective-dependencies ( word -- seq )
    [ load-dependencies ]
    [ "dependency-checks" word-prop
      [ depends-on-method? ] filter [ method>> ] map ]
    bi append
    ;

! The tail sequence from node in stack.
: return-cycle ( node stack -- cycle )
    [ index ] [ tail ] bi ;

! :: (topsort) ( nodes quot: ( node -- children ) accum stack cycles -- add )
!     [
!         dup stack member?
!     ] each

! :: (topsort) ( quot: ( node -- children ) accum stack cycles -- add )


: if-branch ( obj then else -- )
    [ [ branch? ] keep ] 2dip
    bi-curry if ; inline


:: foo ( words -- seq )
    words [
        ! [ ]
        !     [ effective-dependencies words intersect ] if-branch
    ] deep-map ;

! SYMBOLS: word-set visited stack cycles ;

! :: visit ( perm temp stack node cycle -- )
!     node stack index [| i | stack i tailjk ]

! : (topsort) ( quot: ( node -- children ) -- )
!     [ word-set get empty? not ] [
!         word-set get pop :> next
!         next stack get member?
!         [ stack get next index stack swap cut
!           cycles get push
!           stack set ]
!         [ next stack get push
!           next quot call

!         ]
!         dup visited member?
!     ]


! Run through a tree, return nodes in topological order.  Return cycles separately
! : topsort ( tree quot: ( node -- children ) -- nodes cycles )
!     [let
!      V{ } clone :> accum
!      V{ } clone :> stack
!      V{ } clone :> cycles
!      accum stack cycles [ (topsort) ] 3keep
!     ]

! :: (sort-deps) ( accum word -- )
!     word accum ?adjoin
!     [ word effective-dependencies
!       candidates get intersect
!       [ accum swap (sort-deps) ] each ] when
!     ; recursive

! :: sort-deps ( seq -- seq )
!     V{ } clone :> accum
!     seq candidates [
!         seq [ accum swap (sort-deps) ] each
!     ] with-variable
!     accum <reversed>
!     ;

:: add-word ( word graph -- )
    word word graph add-vertex
    word effective-dependencies [
        word swap graph add-edge
    ] each ;

:: <dependency-graph> ( words -- digraph )
    <digraph> :> graph
    words [ graph add-word ] each
    graph ;


ERROR: topological-sort-cycle key trace ;
SYMBOL: cycle-set

: not-in-cycle? ( key -- ? )
    dup cycle-set get in? [ cycle-set get topological-sort-cycle ] when ;

: in-unvisited-set? ( unvisited key -- ? ) swap key? ;
: unvisited? ( unvisited key -- ? ) [ in-unvisited-set? ] [ not-in-cycle? ] bi and ;
: visited ( unvisited key -- ) [ swap delete-at ] [ cycle-set get delete ] bi ;

DEFER: (topological-sort)
: visit-children ( seq unvisited key -- seq unvisited )
    dup cycle-set get adjoin
    over children [ (topological-sort) ] each ;

: (topological-sort) ( seq unvisited key -- seq unvisited )
    2dup unvisited? [
        [ visit-children ] keep 2dup visited pick push
    ] [
        drop
    ] if ;

: topological-sort ( digraph -- seq )
    HS{ } clone cycle-set [
        [ V{ } clone ] dip [ clone ] keep
        [ drop (topological-sort) ] assoc-each drop reverse
    ] with-variable ;

: sort-deps ( seq -- seq )
    <dependency-graph> topological-sort ;
