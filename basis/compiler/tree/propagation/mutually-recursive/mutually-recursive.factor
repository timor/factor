USING: accessors combinators.short-circuit compiler compiler.tree compiler.tree.builder
compiler.tree.cleanup compiler.tree.combinators kernel namespaces sequences ;

IN: compiler.tree.propagation.mutually-recursive

! In contrast to inline-recursive combinators, this pass deals with "regular"
! recursive calls for output value info propagation for single and mutual recursion.

SYMBOL: propagate-recursive?

! * Single Recursive Propagation

! We need to have access to the tree currently being traversed if we want to
! create pruned versions:
SYMBOL: current-nodes

! Track the phi nodes which need to be checked for value info divergence.  LIFO
! stack.
SYMBOL: check-call-sites

! * Splicing of pruned recursive trees for inlining

! ** Keeping Track of spliced call sites

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
    [ drop out-d>> ]
    [ ensure-reject-call ] 2bi
    tree>sub-tree
    ;

! Interfacing with compiler.tree.propagation.inlining

! TODO: replace this with TOS of the recursive compilation trace
: recursive-inline? ( #call -- ? )
    word>> word-being-compiled get =
    propagate-recursive? get and ;

! * Mutually Recursive Propagation

! Similarly to the single recursive variant, we can generalize this to any call
! which does not have output infos available (yet) This would be prohibitively
! expensive if done all the time.  The only cases where this is intended to happen
! when compiling mutually recursive words, which is when:

! - it is part of the same compilation unit
! - the word in question does not have output infos

! This can only happen if nested compilation is impossible because we encountered
! a cycle.  Thus, the condition for propagation-related inlining is that the call
! in question is a part of the nested compilation trace.

: mutual-recursive-inline? ( #call -- ? )
    word>> nested-compilations get member?
    propagate-recursive? get and ;

! Divergence at phi nodes from recursive call sites

! Return t if the info from the recursive call site has a lower lower bound.
: lower-bound-diverges? ( base-case-info recursive-info -- t )
    [ interval>> from>> first ] bi@ > ;

: upper-bound-diverges? ( base-case-info recursive-info -- t )
    [ interval>> to>> first ] bi@ < ;

: infer-divergence ( #phi call-site -- )
    2drop ;
    ! [ [ phi-info-d>> ] [ remaining-branches>> ] bi* ]

: check-phi-divergence ( #phi -- )
    propagate-recursive? get
    [
        check-call-sites get last 2dup phi>> =
        [ infer-divergence ]
        [ 2drop ] if
    ] [ drop ] if
    ;
