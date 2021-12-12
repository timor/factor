USING: accessors arrays assocs assocs.extras columns continuations kernel
kernel.private namespaces quotations sequences sets types.expander
types.protocols types.type-values words ;

IN: types.transitions

FROM: namespaces => set ;
! * Composition of state transitions

! IR for ping/pong inference

! * Traversing transition network

! ** Interleaved with expansion and modular-type-transfer

TUPLE: transfer-record state-in state-out code ;
C: <transfer-record> transfer-record
SYMBOL: transitions
SYMBOL: current-transfer
SYMBOL: current-undo
SYMBOL: inference-word-nesting
SYMBOL: word-transfers

DEFER: infer-word-transfer ! ( word -- transfer )

GENERIC: transfer-quots ( state-in word -- transfer )
: cached-word-transfer ( word -- transfer )
    word-transfers get
    [ [ infer-word-transfer ] cache ]
    [ infer-word-transfer ] if* ;

M: object transfer-quots
    compute-transfer-quots ;

! Throws away state information
M: word transfer-quots
    nip cached-word-transfer ;

PREDICATE: recursive-primitive < word [ def>> ] [ 1quotation ] bi = ;

M: recursive-primitive transfer-quots
    compute-transfer-quots ;

M: primitive-data-op transfer-quots
    compute-transfer-quots ;
M: \ declare transfer-quots
    compute-transfer-quots ;

ERROR: recursive-word-transfer-inference word ;

DEFER: apply-quotation-transfer

! Adds to the variables
: compose-transfers ( quot-assoc quot-assoc -- composed-assoc )
    [ compose ] assoc-merge ;

: prepose-transfers ( quot-assoc quot-assoc -- composed-assoc )
    [ prepose ] assoc-merge ;

! TODO: backprop per branch?
! Yes.  The reason is because we are collecting a new undo quotation.  That is
! only valid until this branch.
! TODO: or more generally, always pong-ping if a declaration has been encountered?
! TODO: or even more generally, always pong-ping if input application has
! changed anything???
DEFER: infer-branch-transfer
DEFER: pong-ping

! : make-parallel-transfer ( out-states transfers -- transfer-assoc )
!     [| dom branch-outs branch-transfers |
!      branch-outs branch-transfers
!      [| out-state branch-transfer i |
!       branch-transfer transfer-in/out :> in out
!       branch-transfer transfer-quots>> dom of :> branch-quot
!       branch-quot in i dom augment-branch-quot

!      ] 2map-index
!      ] 2curry
!     map-domains ;

ERROR: stuck-branch ;
! :: apply-parallel-transfer ( state-in cases -- state-out )
: apply-parallel-transfer ( state-in cases -- state-out )
    dupd [ [ infer-branch-transfer 2array ]
           [ dup divergent-type-transfer? [ 3drop f ] [ rethrow ] if ]
           recover
    ] with map sift
    dup empty? [ stuck-branch ] when
    unzip ! out-states transfers
    [ [ <flipped> [ squish-type-values ] map ] keep ] dip
    [ all-parallel>merge current-transfer [ swap compose-transfers ] change ]
    [ all-parallel<unsplit current-undo [ swap prepose-transfers ] change ]
    [ [ [ records>> ] map <transfer-record> transitions [ swap suffix ] change ]
      keepd ] tri ;

    ! drop ;
    ! state-in pong-ping cases [
    !     infer-branch-transfer
    !     [ 2array ] when*
    ! ] with map sift unzip
    ! :> ( out-states transfers )
    ! ! transfers
    ! ! first3 :> ( trans branch-transfers branch-undos )
    ! all-domains [ dup
    !                 [ transfers [ second ] map [ at ] with map ]
    !                 [ make-disjunctive-transfer ] bi
    ! ] H{ } map>assoc current-transfer [ swap compose-transfers ] change
    ! all-domains [ dup
    !                 [ transfers [ third ] map [ at ] with map ]
    !                 [ make-disjunctive-transfer ] bi
    ! ] H{ } map>assoc current-undo [ swap prepose-transfers ] change
    ! out-states merge-states :> state-out
    ! transitions [
    !     state-in state-out transfers [ first ] map <transfer-record> suffix ] change
    ! state-out
    ! ;


: apply-word-transfer ( state-in word -- state-out )
    [let
     ensure-inputs :> ( state-in word )
     state-in word type-expand :> cases
     cases quotation? [ state-in cases apply-quotation-transfer ]
     [
         cases array?
         [ state-in cases apply-parallel-transfer ]
         [
             state-in word transfer-quots first2 :> ( transfer undo )
             state-in transfer apply-transfers dup :> state-out
             transitions [ state-in state-out word <transfer-record> suffix ] change
             current-transfer [ transfer compose-transfers ] change
             current-undo [ undo prepose-transfers ] change
         ] if
     ] if
    ] ;

: apply-quotation-transfer ( state-in code -- state-out )
    [ apply-word-transfer ] each ;

! Top-level call transfer semantics, input-independent assumption
: compute-word-transfer ( word -- )
    H{ } current-transfer set
    H{ } current-undo set
    transitions off
    f swap def>> apply-quotation-transfer drop ;

: infer-word-transfer ( word -- transfer )
    reset-expansions
    dup inference-word-nesting get in? [ recursive-word-transfer-inference ] when
    [ inference-word-nesting [ over suffix ] change
      compute-word-transfer
      current-transfer get
      current-undo get 2array
    ] with-scope ;

: infer-branch-transfer ( state-in quot -- state-out/f transfer/f )
    [
        H{ } current-transfer set
        H{ } current-undo set
        transitions off
        apply-quotation-transfer
        transitions get
        current-transfer get
        current-undo get <transfer>
    ] with-scope ;

! TODO: dedup!
: ping ( quot -- transfer )
    reset-expansions
    [
        H{ } current-transfer set
        H{ } current-undo set
        transitions off
        f swap apply-quotation-transfer drop
        transitions get
        current-transfer get
        current-undo get <transfer>
    ] with-scope ;

: undo-transfer ( transfer -- state-in )
    [ records>> last state-out>> ] [ undo-quots>> ] bi
    apply-transfers ;

: pong-ping ( state-in -- state-in )
    current-undo get apply-transfers
    current-transfer get apply-transfers ;

: run-quot ( quot -- transfer state-in )
    ping dup undo-transfer ;

: ping-pong ( quot -- transfer state-in state-out )
    ! [ run-quot ] keep
    ! infer-branch-transfer
    ! [ [ first last state-out>> ] dip 2dup = [ drop ] [ "unstable" throw ] if ] dip ;
    run-quot swap dup records>> last state-out>> swapd ;

! First run on the transition, infer the principal input type.  Then re-run the
! compiled type quotations on the new inputs.
: ping-pong-ping ( quot -- in out1 out2 )
    ping-pong [ swap dupd transfer-quots>> apply-transfers ] dip swap ;
