USING: accessors assocs combinators combinators.short-circuit compiler.tree
compiler.tree.builder compiler.tree.cleanup compiler.tree.propagation.info
compiler.utilities fry grouping kernel locals namespaces sequences ;
IN: compiler.tree.propagation.mutually-recursive.pruning

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

! We need to find the branch where the call in question is in.  The corresponding child nodes are marked as dead code, and the phi node which follows needs to be inlined
GENERIC: branch-with-call? ( call node -- flags ? )
M: node branch-with-call? 2drop f f ;
M: #branch branch-with-call?
    children>> [ child-contains-node? not ] with map
    dup [ not ] any? ;

! Like map-nodes, but if an inlined body is detected, traverse this
:: map-nodes-inline ( ... nodes quot: ( ... node -- ... node' ) -- ... nodes )
    nodes [
        quot call
        {
            { [ dup #branch? ] [ [ [ quot map-nodes-inline ] map ] change-children ] }
            { [ dup #recursive? ] [ [ quot map-nodes-inline ] change-child ] }
            { [ dup #alien-callback? ] [ [ quot map-nodes-inline ] change-child ] }
            { [ dup { [ #call? ] [ body>> ] } 1&& ] [ body>> quot map-nodes-inline ] }
            [ ]
        } cond
    ] map-flat ; inline recursive

! Find rcall in nodes, remove branch which it is in, return call site
:: prune-recursive-call ( rcall nodes -- nodes' found )
    f :> found!
    nodes
    [ clone rcall over branch-with-call?
      [
          '[ _ [ and ] 2map ] change-live-branches
          t found!
      ] [ drop ] if
    ] map-nodes-inline cleanup-tree found
    ;

: push-rec-return-infos ( values -- )
    [ [ value-info ] keep rec-return-infos get push-at ] each ;

: get-rec-return-info ( value -- info/f )
    rec-return-infos get at
    [ value-infos-union ]
    [ f ] if* ;

: ensure-reject-call ( call nodes -- nodes )
    prune-recursive-call
    [ "Did not find recursive call" throw ] unless ;

: pruned-recursion-inline-body ( #call nodes -- nodes )
    ! dup q. flush
    [ drop out-d>> ]
    [ ensure-reject-call ] 2bi
    tree>sub-tree
    ! dup q. flush
    ;
