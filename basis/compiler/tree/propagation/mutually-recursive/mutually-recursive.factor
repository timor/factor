USING: accessors combinators.short-circuit compiler.tree compiler.tree.builder
compiler.tree.cleanup compiler.tree.combinators kernel namespaces sequences ;

IN: compiler.tree.propagation.mutually-recursive

! In contrast to inline-recursive combinators, this pass deals with "regular"
! recursive calls for output value info propagation for single and mutual recursion.

SYMBOL: propagate-recursive?

! * Single Recursive Propagation

! We need to have access to the tree currently being traversed if we want to
! create pruned versions:

SYMBOL: current-nodes

! * Splicing of pruned recursive trees for inlining

! ** Creating the replacement nodes

! Return nodes with all branches removed that contain the call.
GENERIC: reject-call* ( call node -- nodes )
M: node reject-call* nip ;

! A call is identical if the output values are the same.
: call= ( node node -- ? )
    { [ [ #call? ] both? ]
      [ [ out-d>> ] bi@ = ] } 2&& ;

: child-contains-node? ( node child-nodes -- ? )
    [ over call= ] any?
    nip
    ;

M: #branch reject-call*
    swap over children>> [ child-contains-node? not ] with map
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
    [ drop out-d>> ]
    [ ensure-reject-call ] 2bi
    tree>sub-tree
    ;

! Interfacing with compiler.tree.propagation.inlining

! TODO: replace this with TOS of the recursive compilation trace
: recursive-inline? ( #call -- ? )
    word>> word-being-compiled get =
    propagate-recursive? get and ;
