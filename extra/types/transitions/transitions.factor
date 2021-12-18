USING: accessors arrays assocs assocs.extras classes classes.algebra columns
combinators continuations effects generalizations kernel kernel.private math
math.parser namespaces quotations sequences sets shuffle strings typed types
types.bidi types.parametric.effects types.protocols types.type-values types.util
words ;

IN: types.transitions

FROM: namespaces => set ;
! * Composition of state transitions
! IR for ping/pong inference

TUPLE: transition state-in state-out code ;
C: <transition> transition

! * Traversing transition network

! ** Interleaved with expansion and modular-type-transfer

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
! M: \ push-types transfer-quots
!     compute-transfer-quots ;

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

! :: apply-parallel-transfer ( state-in cases -- state-out )
: apply-parallel-transfer ( state-in cases -- state-out )
    dupd [ [ infer-branch-transfer 2array ]
           [ dup divergent-type-transfer? [ 3drop f ] [ rethrow ] if ]
           recover
    ] with map sift
    dup empty? [ diverges ] when
    unzip ! out-states transfers
    [ [ <flipped> [ squish-type-values ] map ] keep ] dip
    [ all-parallel>merge current-transfer [ swap compose-transfers ] change ]
    [ all-parallel<unsplit current-undo [ swap prepose-transfers ] change ]
    [ [ [ records>> ] map <transition> transitions [ swap suffix ] change ]
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
    !     state-in state-out transfers [ first ] map <transition> suffix ] change
    ! state-out
    ! ;

! Inferring unknown calls:
! save current state
! perform rest of transfer
! calculate difference
! insert a call-effect

SYMBOL: must-inline?

! : apply-call-transfer ( state-in -- state-out )
!     ! must-inline? on
!     ! [ current-transfer  ]
!     ;
ERROR: non-literal-call ;

! If we see a call-effect without a literal effect, then that's where we
! finally give up... this means we could neither infer it, nor has the user
! provided it
ERROR: call-effect-without-effect ;
ERROR: invalid-call-effect-effect thing ;

! call-effect forward-transfers:
! ..a callable effect → ..b
! 1. drop the effect
! 2. apply the effect-declaration
! 3. drop the callable
! 4. apply all input declarations i1...in
! 5. drop input in ... drop input i1
! 6. push output o1 ... push output om


! call-effect undo-transfers:
! ..a callable effect ← ..b

! 1. apply all output declarations o1...om
! 2. drop output om ... drop output o1
! 3. push all inputs
! 4. push the callable
! 5. push the effect

M: \ call-effect in-types* drop { callable effect } ;

! Here we need to be able to lie!
! We insert a code record which performs the call, but the undo and transfer
! quotations must be created so they work in a coherent manner on their
! respective stacks.
! First apply the class declarations directly to the input state
! :: call-effect-record ( state-in in-values out-values -- state-out transition )
!     ! effect effect>class/type-values :> ( class-in class-out )
!     ! state-in 2 cut* :> ( before-state call-effect-inputs )
!     state-in in-values keys :> dup in-class-decls length pad-state
!     in-class-decls [| type-value decl-value |
!               type-value [ decl-value swap apply-domain-declaration ] map-value-domains
!     ] 2map-suffix :> call-input-state
!     call-input-state class-in length head-slice*
!     out-values values append :> call-output-state
!     call-output-state state-in over
!     effect [ call-effect ] curry <transition>
!     ;

! TYPED: call-effect-produce-record ( state-in: type-stack out-values --
: call-effect-produce-record ( state-in: type-stack out-values --
                               state-out: type-stack )
    values [ append ] keepd over \ call-effect <transition>
    transitions [ swap suffix ] change ;


! ! Remembering Inputs.  These are the absolute base operations, performing invariant
! ! checks.
! : call-effect-lhs ( in-values -- transfer undo )
!     [ [ [ swap make-class-declaration-quot ]
!         [ length [ drop ] n*quot compose ] bi
!       ] curry map-domains ]
!     [ [ [ swap class>domain-value literalize ] with [ ] map-as ] curry map-domains ] bi
!     ;

! ! This one is funny...
! : call-effect-rhs ( class-out -- transfer undo )
!     call-effect-lhs swap ;

: add-transfers ( transfer undo -- )
    [ current-transfer [ swap compose-transfers ] change ]
    [ current-undo [ swap prepose-transfers ] change ] bi* ;

! : add-call-effect-transfers ( in-class-decls out-domain-values -- )
!     [ call-effect-lhs add-transfers ]
!     [ call-effect-rhs add-transfers ] bi* ;

DEFER: apply-word-transfer
TYPED:: apply-consume-transfers ( state-in: type-stack in-values -- state-out: type-stack )
    state-in in-values keys :> in-decls
    in-decls apply-word-transfer
    \ declare apply-word-transfer
    in-decls length [ \ drop apply-word-transfer ] times ;

! Forward: push the values
! Undo: intersect declarations and drop
: add-produce-transfers ( out-values -- )
    [ values unzip-domains [ [ literalize ] [ ] map-as ] map-values ]
    [ keys [ [ swap make-class-declaration-quot ]
             [ length [ drop ] n*quot ] bi compose ] curry map-domains ]
    bi
    add-transfers ;

TYPED: apply-call-effect ( state-in: type-stack -- state-out: type-stack )
    dup 1 macro-literals [ call-effect-without-effect ] unless
    ?last dup effect? [ invalid-call-effect-effect ] unless
    [ [ \ drop apply-word-transfer ] dip ! Drop effect
      <typed-quotation> 1array apply-word-transfer ! Push quotation type
      \ declare apply-word-transfer ! Declare the callable thing to have an effect type
      \ drop apply-word-transfer ! Drop the callable thing
    ] keep
    effect>class/type-values
    [ apply-consume-transfers ] dip
    ! Perform the transitions
    [ call-effect-produce-record ] keep
    ! Compute the domain-specific invariant pushes and pops
    add-produce-transfers ;

TYPED: apply-word-transfer ( state-in: type-stack word -- state-out: type-stack )
    [let
     ensure-inputs :> ( state-in word )
     state-in word type-expand :> cases
     cases callable? [ state-in cases apply-quotation-transfer ]
     [
         cases array?
         [ state-in cases apply-parallel-transfer ]
         [
             word \ call eq?
             [ non-literal-call ]
             [
                 word \ call-effect eq?
                 [ state-in apply-call-effect ]
                 [
                     state-in word transfer-quots first2 :> ( transfer undo )
                     state-in transfer apply-transfers dup :> state-out
                     transitions [ state-in state-out word <transition> suffix ] change
                     current-transfer [ transfer compose-transfers ] change
                     current-undo [ undo prepose-transfers ] change
                 ] if
             ] if
         ] if
     ] if
    ] ;

DEFER: apply-quotation-transfer
SYMBOLS: stack-id stack-id-in stack-id-out ;
: assume-new-stack ( -- )
    stack-id counter
    [ stack-id-in set ]
    [ stack-id-out set ] bi ;

: init-straight-line-inference ( -- )
    H{ } current-transfer set
    H{ } current-undo set
    transitions off ;


DEFER: stacks>effect
! :: compute-call-effect ( state-in state-out-2 rest-transitions transfers undos -- state-out )
!     state-out-2 undos apply-transfers :> state-in-2
!     state-in state-in-2 drop-prefix stacks>effect :> effect
!     state-in effect apply-word-transfer
!     \ call-effect apply-word-transfer drop
!     transitions [ rest-transitions append ] change
!     current-transfer [ transfers compose-transfers ] change
!     current-undo [ undos prepose-transfers ] change
!     state-out-2 ;

:: compute-call-effect ( state-in state-out-2 rest-transitions transfers undos -- state-out )
    state-out-2 undos apply-transfers :> state-in-2
    state-in state-in-2 stacks>effect :> effect
    state-in effect apply-word-transfer
    \ call-effect apply-word-transfer drop
    transitions [ rest-transitions append ] change
    current-transfer [ transfers compose-transfers ] change
    current-undo [ undos prepose-transfers ] change
    state-out-2 ;

: splice-call-effect ( rest state-in -- state-out )
    must-inline? on
    swap [
        assume-new-stack
        init-straight-line-inference
        f swap apply-quotation-transfer
        transitions get
        current-transfer get
        current-undo get
        stack-id-out get
    ] with-scope
    stack-id-out set
    compute-call-effect
    ;

: apply-quotation-transfer ( state-in code -- state-out )
    [| c state-in code |
     state-in code
        [ [ nip apply-word-transfer ]
          [ dup non-literal-call?
            [ 2drop rest swap splice-call-effect c continue-with ]
            [ rethrow ] if
          ] recover
        ] each-with-rest
    ] 2curry callcc1
    ;

! Top-level call transfer semantics, input-independent assumption
: compute-word-transfer ( word -- )
    init-straight-line-inference
    f swap def>> apply-quotation-transfer drop ;

: infer-word-transfer ( word -- transfer )
    reset-expansions
    dup inference-word-nesting get in? [ recursive-word-transfer-inference ] when
    [
        must-inline? off
        inference-word-nesting [ over suffix ] change
        compute-word-transfer
        current-transfer get
        current-undo get 2array
    ] with-scope ;

: capture-transfer ( -- transfer )
    transitions get
    current-transfer get
    current-undo get <transfer>
    stack-id-in get >>id-in
    stack-id-out get >>id-out ;

: infer-branch-transfer ( state-in quot -- state-out/f transfer/f )
    [
        init-straight-line-inference
        apply-quotation-transfer
        capture-transfer
    ] with-scope ;

! TODO: dedup!
: ping ( quot -- transfer )
    reset-expansions
    [
        assume-new-stack
        init-straight-line-inference
        f swap apply-quotation-transfer drop
        capture-transfer
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

: run-pass ( input-state quot -- input-state quot/transfer dead-branches? )
    ! reset-expansions
    [
        init-straight-line-inference
        assume-new-stack
        [ apply-quotation-transfer ] keep
        [
            current-undo get
            apply-transfers
            stuck-transfers get
        ] dip swap
        [ [ drop capture-transfer ] unless ] keep
    ] with-scope ;

: infer-transfer ( quot -- inputs transfer )
    f swap [ run-pass ] loop ;

: dependent-ids ( value-ids -- value-ids )
    H{ } clone swap [ over inc-at ] each
    [ 1 > ] filter-values keys ;

: state-var-names ( state-in state-out -- assoc )
    [ [ value-id of members ] map concat [ ??? ] reject ] bi@ append
    dependent-ids
    [ CHAR: a H{ } clone ] dip
    [ [ [ [ 1 + ] keep 1string ] 2dip swap set-at ] with each ]
    keepd nip ;

! TODO: include other domains?
: state>configuration ( names types -- seq )
    [
        [ value-id of
          members [ ??? ] reject
          [ of ] with map sift
          [ f ] [ "|" join ] if-empty
        ]
        [ class of dup ???
          [ drop ]
          [ dup effect-type?
            [ effect>> ] when 2array
           ] if
        ] bi ] with map ;

: <maybe-variable-effect> ( in out -- effect )
    stack-id-in get
    stack-id-out get 2dup = [ 2drop <effect> ]
    [ [ number>string ] bi@ 2swap swapd <variable-effect> ] if ;

: stacks>effect ( state-in state-out -- effect )
    2dup state-var-names
    [ swap state>configuration { } or ] curry bi@
    <effect> ;

: stacks>bivariable-effect ( state-in state-out -- effect )
    2dup state-var-names
    [ swap state>configuration { } or ] curry bi@
    stack-id-in get stack-id-out get  [ number>string ] bi@ 2swap swapd <variable-effect> ;

: transfer>effect ( inputs transfer -- effect )
    [
        [ id-in>> stack-id-in set ]
        [ id-out>> stack-id-out set ]
        [ records>> last state-out>>
        ] tri stacks>effect
    ] with-scope ;


: infer-type ( quot -- effect )
        infer-transfer
        transfer>effect ;
