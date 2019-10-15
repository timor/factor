USING: accessors arrays assocs combinators combinators.short-circuit
compiler.tree compiler.tree.combinators
compiler.tree.propagation.mutually-recursive.branch-overrides compiler.utilities
delegate grouping kernel locals math.vectors namespaces sequences words ;
IN: compiler.tree.propagation.mutually-recursive.pruning
FROM: compiler.tree.propagation.branches => live-branches ;

! * Splicing of pruned recursive trees for inlining

! ** Creating the replacement tree

! Like map-nodes, but over #branch-#phi pairs.
:: map-branches ( ... nodes quot: ( ... #branch #phi -- ... #branch' ) -- ... nodes )
    nodes f suffix 2 clump [
        first2 over #branch? [ quot call ] [ drop ] if
        {
            { [ dup #branch? ] [ [ [ quot map-branches ] map ] change-children ] }
            { [ dup #recursive? ] [ [ quot map-branches ] change-child ] }
            { [ dup #alien-callback? ] [ [ quot map-branches ] change-child ] }
            [ ]
        } cond
    ] map-flat ; inline recursive

! A call is identical if the output values are the same.
: call= ( node node -- ? )
    { [ [ #call? ] both? ]
      [ [ out-d>> ] bi@ = ] } 2&& ;

! Same for a phi
: phi= ( node node -- ? )
    { [ [ #phi? ] both? ]
      [ [ out-d>> ] bi@ = ] } 2&& ;

: child-contains-node? ( node child-nodes -- ? )
    [ over call= ] any?
    nip ;

! Like each-node, but if an inlined body is detected, traverse this
:: each-node-inline ( ... nodes quot: ( ... node -- ... ) -- ... )
        nodes [
            quot
            [
                {
                    { [ dup #branch? ] [ children>> [ quot each-node-inline ] each ] }
                    { [ dup #recursive? ] [ child>> quot each-node-inline ] }
                    { [ dup #alien-callback? ] [ child>> quot each-node-inline ] }
                    { [ dup { [ #call? ] [ body>> ] } 1&& ] [ body>> quot each-node-inline ] }
                    [ drop ]
                } cond
            ] bi
        ] each ; inline recursive

! Like map-nodes, but if an inlined body is detected, traverse this
:: map-nodes-inline ( ... nodes quot: ( ... node -- ... node' ) -- ... nodes )
    nodes [
        quot call
        {
            { [ dup #branch? ] [ [ [ quot map-nodes-inline ] map ] change-children ] }
            { [ dup #recursive? ] [ [ quot map-nodes-inline ] change-child ] }
            { [ dup #alien-callback? ] [ [ quot map-nodes-inline ] change-child ] }
            { [ dup { [ #call? ] [ body>> ] } 1&& ] [ [ quot map-nodes-inline ] change-body ] }
            [ ]
        } cond
    ] map-flat ; inline recursive


! We need to find the branch where the call in question is in.  The
! corresponding child nodes are marked as dead code, and the phi node which
! follows needs to be inlined.
GENERIC: branch-with-call? ( call node -- flags ? )
M: node branch-with-call? 2drop f f ;
M: #branch branch-with-call?
    children>> [ child-contains-node? ] with map
    dup [ ] any? ;

! ** Add #branch children with recursive call sites to overrides
! Find recursive branches leading to call site, so that it can be registered for
! non-traversal in subsequent inlined-body propagation passes.  Returns { branch flags } pairs.
:: get-recursion-branches ( rcall nodes -- pairs )
    V{ } clone nodes [
        rcall over branch-with-call?
        [ 2array suffix! ] [ 2drop ] if
    ] each-node-inline ;

: (add-recursion-branch-overrides) ( pairs -- )
    [ first2 swap add-branch-overrides ] each ;

! Find rcall in nodes, mark branches which it is in, return whether it has been found
: add-recursion-branch-overrides ( rcall nodes -- found )
    get-recursion-branches
    [ (add-recursion-branch-overrides) ]
    [ empty? not ] bi ;

: push-rec-return-infos ( infos values -- )
    [ rec-return-infos get last push-at ] 2each ;

: get-rec-return-infos ( value -- infos/f )
    rec-return-infos get last at ;

: ensure-reject-call ( call nodes -- nodes )
    tuck
    add-recursion-branch-overrides
    [ "Did not find recursive call" throw ] unless ;

: pruned-recursion-inline-body ( #call nodes -- nodes )
    ! dup q. flush
    ensure-reject-call
    [ clone ] map-nodes
    ! dup q. flush
    ;
