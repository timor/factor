USING: ;

IN: compiler.tree.propagation.mutually-recursive

! In contrast to inline-recursive combinators, this pass deals with "regular"
! recursive calls for output value info propagation for single and mutual recursion.


! * Single Recursive Propagation

! We need to have access to the tree currently being traversed if we want to
! create pruned versions:

SYMBOL: current-nodes ;

! * Splicing of pruned recursive trees for inlining

! ** Creating the replacement nodes

! Return nodes with all branches removed that contain the call.
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

: reject-call ( call nodes -- nodes )
    [ reject-call* ] with map-nodes ;

! Interfacing with compiler.tree.propagation.inlining

: pruned-recursion-inline-body ( #call -- nodes )
    current-nodes get reject-call ;

! TODO: replace this with TOS of the recursive compilation trace
: recursive-inline? ( #call -- ? )
    word>> word-being-compiled-get = ;
