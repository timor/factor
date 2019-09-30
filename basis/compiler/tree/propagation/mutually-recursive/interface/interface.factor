USING: accessors compiler compiler.tree kernel namespaces sequences ;

IN: compiler.tree.propagation.mutually-recursive.interface

SYMBOL: propagate-recursive?

! * Single Recursive Propagation

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
