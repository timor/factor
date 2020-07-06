! Copyright (C) 2008, 2010 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays byte-arrays classes classes.algebra classes.tuple
classes.tuple.private combinators combinators.short-circuit compiler.tree
compiler.tree.propagation.copy compiler.tree.propagation.info
compiler.tree.propagation.nodes graphs kernel locals math math.intervals
namespaces sequences sets slots.private sorting strings words ;
IN: compiler.tree.propagation.slots

! * Optimizing Local Slot Accesses

! Rationale: For a given tree of nodes, once we encounter a set-slot call, we
! can assume the output info of any slot-call to that same tuple/array to be
! that, until another set-slot call is encountered.  In a true asynchronous
! multithreading context, we would have to "delete" that assumption if there is
! any synchronization primitive before a slot call.

! TODO: maybe use eq? instead of =
PREDICATE: slot-call < #call word>> \ slot = ;
PREDICATE: set-slot-call < #call word>> \ set-slot = ;
PREDICATE: tuple-boa-call < #call word>> \ <tuple-boa> = ;

! * Implementation Strategy
! The `slot-states` context variable holds mappings from SSA-values representing
! instances (tuples, TODO arrays) and slots to a value, to a pair representing
! the value specifier $val$ and the info of $slot$ at the time of access:
! $obj → slot → val$.  This is local to linear control flow, and
! updated every time a `set-slot` call is encountered.  Note that we include in
! $val$ the information to discern whether this is an SSA Value, or we only have
! the value-info of the slot contents (see below).

! Whenever a `slot` call is encountered, this object is queried, and if the slot
! matches (see below), the value is used to set the output info.

! Note that the reference to $slot$ and $val$ can be SSA values as long there is
! only linear code.  This allows us to treat the output value of a `slot` call as
! a copy of the input to the `set-slot` call.  This is important, since there are
! two things that we want to be able to tell:
! 1. What is the value info of the `slot` call output?
! 2. Is the `slot` call output actually a copy of something we already know?

! The first case's importance is obvious, as we want to be able to perform the
! typical type inference.  The second case is important for a different reason:
! Given e.g. tuple $T_1$ with slot $a$, and tuple $T_2$ with slot $b$, consider
! the following sequence:
! #+begin_example
! foo → T_1.a
! T_1.a -> T_2.b
! ...
! T_2.b -> X
! X.a
! #+end_example
! In this case, we want to be able to detect that the result of the last access is
! in fact the same value as $foo$.  This case is not uncommon, as a lot of
! combinators are implemented using `curried` tuples, which then contain the
! object in question.

! To summarize the strategy:
! 1. If we can prove that a slot access contains a copy of a value, use the copy
!    mechanism
! 2. If we can not prove that a slot access contains a copy of a value, but have
!    input information for the current slot state, use at least this information
!    for output type detection.

! The first case is the strongest, and type inference works as expected since any
! `value-info` call resolves the copies.  The second case could be implemented in
! two ways: (a) Using the value-info on the `slots` slot of the actual value,
! (b) looking up the info in the context on `slot` calls.

! Implementing (a) would mean carefully considering existing slot propagation as
! to how to extend the current mechanism, which is only invoked for read-only
! slots.  (b) is independent of that, since it would be implemented using the
! constraint mechanism of the `slot` call.

! In both cases, the copy information needs to be handled in a special way, since
! there is no infrastructure at the moment which can trace copies out of
! branches.  As with all other local state variables containing information, it
! must be merged at `#phi` nodes.  There are two general cases here:

! 1. Slot accesses in all branches return the same SSA value (after resolving
!    copies)
! 2. Slot access in all branches can return different SSA values.

! In the former case, we can keep the information that the slot still contains a
! copy of a unique known SSA value.  In the latter case, we have to resolve and
! merge value infos, as is done for regular phi outputs.

! ** Equivaluence of Slot Accesses

! Two slot accesses are considered to refer to the same value when
! - The $obj$ SSA-values are resolved to the same copy, and
!   1. The $slot$ SSA-values are resolved to the same copy, or
!   2. The value info of the $slot$ values are identical at the time of the slot
!      accesses.

! The first case allows us to track non-literal accesses as well as literal slot accesses.


SYMBOL: slot-states
! NOTE: Initializing here to be able to call refresh-all from master branch image
slot-states [ V{  } clone ] initialize
TUPLE: slot-state copy-of value-info obj-value obj-info slot-value slot-info ;

! Return the value which the slot contains a copy of, f otherwise
: slot-copy ( slot-state -- value/f )
    copy-of>> dup length 1 = [ first ] [ drop f ] if ;

: <slot-state> ( value-val obj-val slot-val -- obj )
    [ [ 1array ] [ value-info ] bi ]
    [ dup value-info ]
    dup tri* slot-state boa ;

: <unknown-slot-state> ( obj-val slot-val -- obj )
    [ { } clone object-info ] 2dip [ dup value-info ] bi@ slot-state boa ;

: <tuple-boa-slot-state> ( value-val tuple-val slot-n -- obj )
    [ [ 1array ] [ value-info ] bi ] dup [ <literal-info> f swap ] tri* slot-state boa ;

! Merging slot states:  During different branches, different slot accesses could
! have been made.

! When updating slots, perform alias analysis.

SYMBOLS: +same-slot+ +unrelated+ +may-alias+ ;

! | Objects                     | Slots                       | Merged Slot-Value-Info | Relation  |
! |-----------------------------+-----------------------------+------------------------+-----------|
! | both literal, different     | X                           | X                      | unrelated |
! | provably different classes  | X                           | X                      | unrelated |
! | X                           | some literal                | Null                   | unrelated |
! | same                        | both non-literal, same      | not Null               | same-slot |
! | same                        | both non-literal, different | Singular               | same-slot |
! | same                        | both literal                | Singular               | same-slot |
! | one literal                 | X                           | not Null               | may-alias |
! | both non-literal, different | X                           | not Null               | may-alias |
! | same                        | both non-literal, different | Interval               | may-alias |
! | same                        | some literal                | Interval               | may-alias |

: same-object? ( s1 s2 -- ? ) [ obj-value>> ] bi@ = ;

: literal-object? ( state -- ? ) obj-info>> literal?>> ;

: literal-slot? ( state -- ? ) slot-info>> literal?>> ;

! Symbolic equivalence, not value equivalence!
: same-slot? ( s1 s2 -- ? ) [ slot-value>> ] bi@ = ;

: different-object-classes? ( state1 state2 -- ? )
    [ obj-info>> class>> ] bi@
    compare-classes +incomparable+ = ;

: merged-slot-interval ( state1 state2 -- interval )
    [ slot-info>> interval>> ] bi@ interval-intersect ;

! Determine relation between two slot accesses according to the table.
! Can be optimized to not make all tests beforehand if necessary
:: compare-slot-states ( s1 s2 -- symbol )
    s1 s2 same-object? :> same-obj?
    s1 s2 [ literal-object? ] both? :> both-literal?
    s1 s2 [ literal-object? ] either? :> some-literal?
    s1 s2 [ literal-slot? not ] both? :> both-slots-non-literal?
    s1 s2 [ literal-slot? ] both? :> both-slots-literal?
    s1 s2 same-slot? :> same-slot-value?
    s1 s2 different-object-classes? :> disjunct-classes?
    s1 s2 merged-slot-interval :> merged-interval
    { { [ both-literal? same-obj? not and ] [ +unrelated+ ] }
      { [ disjunct-classes? ] [ +unrelated+ ] }
      { [ merged-interval empty-interval? ] [ +unrelated+ ] }
      { [ same-obj? both-slots-non-literal? and
          same-slot-value? and ] [ +same-slot+ ] }
      { [ same-obj? both-slots-non-literal? and
          merged-interval interval-singleton? and ] [ +same-slot+ ] }
      { [ same-obj? both-slots-literal? and
          merged-interval interval-singleton? and ] [ +same-slot+ ] }
      [ +may-alias+ ]
    } cond ;

! * Updating Slot State

! Whenever a set-slot call is encountered, add a slot-state entry to the list.
! Remove all prior states which reference the same value.

: update-slot-state ( slot-state -- )
    dup slot-states get [ compare-slot-states +same-slot+ = ] with reject!
    push ;

: slot-call-update-slot-state ( value-val obj-val slot-val -- )
    <slot-state> update-slot-state ;

! * Querying Slot State

! When accessing a slot value via `slot`, but also (TODO verify) when unifying
! aliasing info at #phi nodes, the procedure to determine the current slot value
! is as follows:
! - Initialize new slot state with null info and the given object and slot values
! - Iterate over the slot-states list in reverse, for each entry compare:
!   - If the object value (copy-of) and the slot value match, return that as base case
!   - If the state may alias, collect entry.
!   - Otherwise ignore entry
! - Then reduce slot-state union over the collected entries in forward order.  At
!   this point, only `+may-alias+` entries should be present.  The unification is
!   as follows:
!   - If the object value differs (copy-of), store the additional copy.
!   - expand the state using value-info-union with the corresponding entry.

:: unify-states ( base-state state -- state' )
    base-state clone
    [ state copy-of>> union natural-sort ] change-copy-of
    [ state value-info>> value-info-union ] change-value-info ;

! Search seq in reverse until comparison with QUERY-STATE returns +same-slot+.
! Return a sequence of all slot-states that may alias during the backwards
! search, with either the +same-slot+ state or QUERY-STATE appended, if no
! +same-slot+ has been found.
:: select-aliasing-read ( seq query-state -- seq )
    [ query-state compare-slot-states +may-alias+ = ] selector :> ( picker accum )
    seq [ picker keep query-state compare-slot-states +same-slot+ = ] find-last nip [ query-state ] unless*
    accum swap suffix ;

! Return the slot state of a slot read access for a given obj-value and slot-value
: slot-query-state ( obj-value slot-value -- state )
    <unknown-slot-state>
    slot-states get swap select-aliasing-read
    [ ] [ unify-states ] map-reduce ;

: get-slot-call-state ( node -- state )
    in-d>> resolve-copies first2 slot-query-state ;

! * Update Slot Call Node Information

! TODO: update copy info when branching works correctly
: refine-slot-call-outputs ( node -- )
    [ out-d>> first ] keep
    get-slot-call-state [ value-info>> ] [ slot-copy ] bi
    [ 2drop ]
    [ swap refine-value-info ] if ;

! * Remove Assumptions when tuple escapes

ERROR: internal-slot-invalidation-error ;

: obj-value-slot-states ( obj-value -- slot-states )
    resolve-copy slot-states get [ obj-value>> = ] with filter ;

! Slot states which would have to be considered written to if the one given here has been written to
: aliasing-slot-states ( slot-state -- slot-states )
    slot-states get [ compare-slot-states +unrelated+ = not ] with filter ;

! If the contents of a slot state are written to, and the content represents a
! slot we are tracking, then we would have to consider these objects to be
! invalid as well
: dependent-slot-states ( slot-state -- slot-states )
    copy-of>> [ obj-value-slot-states ] map concat ;

: all-dependent-slot-states ( slot-state -- slot-states )
    [ aliasing-slot-states dup [ dependent-slot-states ] map concat union ] closure
    members ;

! Remove the slot state from the list, and any which are dependent on it
: invalidate-slot-state ( slot-state -- )
    all-dependent-slot-states slot-states get swap diff! drop ;

! For any object that we assume to know anything about its slots, if it is
! passed to a call, we have to assume that it does whatever with the values, so
! we delete the slot states and any that it may alias to.
: invalidate-slot-states ( #call -- )
    in-d>> resolve-copies [ obj-value-slot-states [ invalidate-slot-state ] each
    ] each ;

: call-invalidate-slot-states ( #call -- )
    dup
    { [ body>> ] [ word>> \ set-slot eq? ] [ word>> foldable? ] [ word>> flushable? ] } 1||
    [ drop ] [ invalidate-slot-states ] if ;

! * Merge Slot States at #phi nodes

! Like other control-flow related context, slot states of different execution
! branches need to be merged at #phi nodes.  This works as follows:
! - Map each member of the merged set of slot-states:
!   - For each other member of the merged set:
!     - compare both, if either 'same-slot' or 'may-alias', unify


! From a sequence of slot-states sequences, compute the slot-states which
! represent the union of all of those
:: merge-slot-states ( seq -- states )
    ! NOTE: for some reason, members of <merged> returns something different
    ! than members of concat!
    ! seq <merged> dup :> all-states
    seq concat members dup :> all-states
    [| base-state | all-states [ base-state compare-slot-states +unrelated+ = ] reject
        base-state [ unify-states ] reduce
    ] map members ;

! * TODO Update slot value info for known copies of

! In order to be able to track identities through local slot accesses, the value
! copy information must be updated.  Copy information usually comes into play
! before propagation of #renaming nodes.
! We should be actually be able to support this by letting a `slot`
! #call behave like a #renaming node.

! TODO Care must be taken to not mess up value info annotation here.  E.g. if we
! update value-info, this is always traced back to the resolved copy.

! This means there are two cases for a `slot` #call
! 1. We prove that this is just a copy of an existing value
! 2. We don't prove that this is just a copy of an existing value

! In the second case, we simply behave like any #call node should, and set the
! value info on the output values.
! In the first case, we additionally behave like a #renaming node first.  This
! means that when we update the value information, we would overwrite/narrow the
! existing value information if it differs (TODO: build in check whether it differs).
! So we don't update the value information on the value itself, but we can
! annotate the #call node's output information without changing the value-info state.

: slot-call-compute-copy-equiv* ( node -- )
    [ get-slot-call-state slot-copy ]
    [ out-d>> first ] bi
    over [ is-copy-of ] [ 2drop ] if ;

M: slot-call compute-copy-equiv*
    [ call-next-method ] keep
    slot-call-compute-copy-equiv*
    ! drop
    ;


! -- End of slot-state stuff

: sequence-constructor? ( word -- ? )
    { <array> <byte-array> (byte-array) <string> } member-eq? ;

: propagate-sequence-constructor ( #call word -- infos )
    [ in-d>> first value-info ]
    [ "default-output-classes" word-prop first ] bi*
    <sequence-info> 1array ;

: fold-<tuple-boa> ( values class -- info )
    [ [ literal>> ] map ] dip slots>tuple
    <literal-info> ;

! Return a seq with only these value infos which belong to a read-only slot.
: read-only-slots ( values class -- slots )
    all-slots
    [ read-only>> [ value-info ] [ drop f ] if ] 2map
    f prefix ;

! The first slot seems to be reserved for an array length, always.  Because of
! that, it is ignored here.  Identity-tuples are not folded in any case.
: fold-<tuple-boa>? ( values class -- ? )
    [ rest-slice [ dup [ literal?>> ] when ] all? ]
    [ identity-tuple class<= not ]
    bi* and ;

: (propagate-<tuple-boa>) ( values class -- info )
    [ read-only-slots ] keep 2dup fold-<tuple-boa>?
    [ [ rest-slice ] dip fold-<tuple-boa> ] [ <tuple-info> ] if ;

: propagate-<tuple-boa> ( #call -- infos )
    in-d>> unclip-last
    value-info literal>> first (propagate-<tuple-boa>) 1array ;

: read-only-slot? ( n class -- ? )
    all-slots [ offset>> = ] with find nip
    dup [ read-only>> ] when ;

! This one is called when the slot and the object are literal..., but only on
! read-only slots.  Note that the mechanism which records local slot accesses
! during propagation has some overlap with this.
: literal-info-slot ( slot object -- info/f )
    {
        [ class-of read-only-slot? ]
        [ nip layout-up-to-date? ]
        [ swap slot <literal-info> ]
    } 2&& ;

! This one is called when a literal slot number has been supplied to a slot call
: value-info-slot ( slot info -- info' )
    {
        { [ over 0 = ] [ 2drop fixnum <class-info> ] } ! I think this the array ! length accessor case...
        { [ dup literal?>> ] [ literal>> literal-info-slot ] }
        [ [ 1 - ] [ slots>> ] bi* ?nth ]
    } cond [ object-info ] unless* ;

: set-slot-call-propagate-after ( node -- )
    in-d>> resolve-copies first3 slot-call-update-slot-state ; inline

! Inputs: value obj n
M: set-slot-call propagate-after
    [ set-slot-call-propagate-after ] keep
    call-next-method ;

: tuple-boa-call-propagate-after ( node -- )
    [ out-d>> ]
    [ in-d>> but-last resolve-copies ] bi
    [| in-value out-value slot-n |
     in-value out-value slot-n 1 + <tuple-boa-slot-state> update-slot-state
    ] with each-index ;

M: tuple-boa-call propagate-after
    [ tuple-boa-call-propagate-after ] keep
    call-next-method ;
