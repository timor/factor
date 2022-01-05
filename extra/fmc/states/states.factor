USING: accessors arrays assocs fmc kernel lists math namespaces
persistent.assocs quotations sequences typed types.util ;

IN: fmc.states

! * Machine states

! PREDICATE: fmc-stack < sequence [ fmc-term? ] all? ;
! PREDICATE: fmc-stack < sequence [ fmc-seq? ] all? ;
UNION: fmc-stack fmc-seq ;
PREDICATE: fmc-memory < assoc
    [ nip fmc-stack? ] assoc-all? ;

TUPLE: fmc-state
    { memory fmc-memory read-only }
    { term fmc-term read-only initial: +nil+ } ;
C: <fmc-state> fmc-state

TYPED: init-fmc-state ( term: fmc-term -- state: fmc-state )
    H{ } swap <fmc-state> ;

TYPED: >fmc-state ( quot: callable -- state: fmc-state )
    >fmc beta
    init-fmc-state ;

TYPED: head-term ( state: fmc-state -- term/f: maybe{ fmc-seq-term } )
    term>> [ f ] { [ nip ] } lmatch ; inline

TYPED: loc-item ( state: fmc-state loc -- term/f: maybe{ fmc-seq-term } )
    swap memory>> at ;

PREDICATE: application-state < fmc-state
    head-term loc-push? ;

PREDICATE: abstraction-state < fmc-state
    head-term loc-pop? ;
PREDICATE: non-stuck-abstraction < abstraction-state
    [ head-term loc>> ] [ swap loc-item ] bi ;

! TODO: run naked primitives on the default stack?
! - Or maybe compose machine states here?
! PREDICATE: primitive-exec-state < fmc-state
!     head-term fmc-prim? ;

! PREDICATE: non-stuck-primitive < primitive-exec-state
!     head-term

! Primitive machine transitions are delegated to the corresponding stacks as folding operations

UNION: non-stuck-state application-state non-stuck-abstraction ;

GENERIC: step-fmc* ( state: fmc-state -- memory: fmc-memory term: fmc-term )

TYPED:: check-confluence ( state: fmc-state state': fmc-state continue?: boolean --
                          state': fmc-state continue?: boolean )
    continue?
    [ state state' =
      [ state state' "fmc-step-didnt-change-state" 3array throw ]
      [ state' t ] if
    ]
    [ state' f ] if ;

TYPED: safe-step-fmc ( state: fmc-state -- state': fmc-state continue?: boolean )
    dup step-fmc* <fmc-state> dup non-stuck-state?
    check-confluence ;

TYPED: step-fmc ( state: fmc-state -- state': fmc-state continue?: boolean )
    step-fmc* <fmc-state>
    dup non-stuck-state? ;

M: fmc-state step-fmc* [ memory>> ] [ term>> ] bi ;

TYPED: pop-loc-mem ( mem: fmc-memory loc -- mem': fmc-memory item: fmc-seq-term )
    [ pluck-at ] [ at ] 2bi ;

M: non-stuck-abstraction step-fmc*
    call-next-method unswons swap
    [ [ loc>> pop-loc-mem ] [ var>> ] bi ] dip
    beta-subst ;

! Pushing term with continuation on stack is kind of a with-stack-run
! TODO: instead of just appending, this would also perform folds!
TYPED: with-fmc-stack ( stack: fmc-stack term: fmc-term -- stack: fmc-stack )
    [ suffix ] leach ;

M: application-state step-fmc*
    call-next-method unswons swap
    [ [ loc>> ] [ body>> ] bi swapd '[ _ with-fmc-stack ] changed-at ] dip ;

PREDICATE: fmc-trace < sequence [ fmc-state? ] all? ;

SYMBOL: watchdog

TYPED: run-fmc ( state: fmc-state -- trace: fmc-trace )
    0 watchdog [
        watchdog get 100 > [ "runaway fmc" 2array throw ] [ watchdog inc ] if
        [ safe-step-fmc ] [ dup ] produce swap suffix
    ] with-variable
    ;
