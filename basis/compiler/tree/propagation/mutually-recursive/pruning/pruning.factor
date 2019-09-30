USING: accessors combinators.short-circuit compiler.tree compiler.tree.builder
compiler.tree.cleanup compiler.tree.combinators kernel math namespaces sequences
;
IN: compiler.tree.propagation.mutually-recursive.pruning

! * Splicing of pruned recursive trees for inlining

! ** Keeping Track of spliced call sites

! Track the phi nodes which need to be checked for value info divergence.  LIFO
! stack.
SYMBOL: check-call-sites


! Store information on the #branch/#phi pairs that have been removed during pruning
TUPLE: inlined-call-site
    branch
    phi
    remaining-branches ;

: <inlined-call-site> ( branch remaining-branches -- obj )
    inlined-call-site new
    swap >>remaining-branches
    swap >>branch ;

! Complete call site info
: complete-call-site ( nodes obj -- obj )
    [ branch>> swap [ index 1 + ] keep nth ] keep
    swap >>phi ;

! If we have an incomplete call site info on TOS, the last reject-call* pruned
! a #branch
: complete-last-call-site ( nodes -- )
    check-call-sites get last
    dup phi>> [ 2drop ] [ complete-call-site drop ] if ;

! ** Creating the replacement tree

! Return nodes with all branches removed that contain the call.
GENERIC: reject-call* ( call node -- nodes )
M: node reject-call* nip ;

! A call is identical if the output values are the same.
: call= ( node node -- ? )
    { [ [ #call? ] both? ]
      [ [ out-d>> ] bi@ = ] } 2&& ;

! Same for phi nodes
! TODO: check if this can be generalized
: phi= ( node node -- ? )
    { [ [ #phi? ] both? ]
      [ [ out-d>> ] bi@ = ] } 2&& ;

: child-contains-node? ( node child-nodes -- ? )
    [ over call= ] any?
    nip
    ;

M: #branch reject-call*
    swap over children>> [ child-contains-node? not ] with map
    [ dup [ not ] any?
      [ <inlined-call-site> check-call-sites get push ]
      [ 2drop ] if ] 2keep
    >>live-branches ;

M: #if reject-call* call-next-method ;

: reject-call ( call nodes -- nodes )
    [ clone ] map-nodes
    [ reject-call* ] with map-nodes
    cleanup-tree
    ;

! If we didn't change any nodes, this is an error
ERROR: infinite-recursion-error ;
: ensure-reject-call ( call nodes -- nodes )
    [ reject-call ] keep
    2dup = [ infinite-recursion-error ] [ drop ] if ;

: pruned-recursion-inline-body ( #call -- nodes )
    current-nodes get
    ! dup q. flush
    [ drop out-d>> ]
    [ ensure-reject-call ] 2bi
    tree>sub-tree
    ! dup q. flush
    ;
