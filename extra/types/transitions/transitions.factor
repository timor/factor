USING: accessors arrays assocs assocs.extras classes classes.algebra columns
combinators combinators.short-circuit continuations generic generic.math
generic.single kernel namespaces quotations sequences sets types.bidi
types.expander types.protocols types.type-values words ;

IN: types.transitions

FROM: namespaces => set ;
! * Composition of state transitions

! IR for ping/pong inference

! ** Transition element
TUPLE: transition
    word state-in state-out ! prev next
    id ;

: new-transition ( word class -- obj )
    new swap >>word
    \ transition counter >>id
    ;

: init-state ( transition word -- transition )
    [ in-types >>state-in ]
    [ out-types >>state-out ] bi ;

: <atomic-transition> ( word -- obj )
    transition new-transition ;

: <preset-atomic-transition> ( word -- obj )
    [ <atomic-transition> ]
    [ init-state ] bi ;


TUPLE: parallel-transition < transition bodies ;

: init-unknown-state ( transition word -- transition )
    [ in-types length ?? <array> >>state-in ]
    [ out-types length ?? <array> >>state-out ] bi ;

! Better call a checking implementation instead if disjoint behavior is needed...
: <parallel-transition> ( word cases -- obj )
    [
        [ parallel-transition new-transition ]
        [ init-state ] bi
    ] dip >>bodies ;

! Specs are: { configuration quotation } pairs
! : <disjoint-parallel> ( specs --  )

: <inline-transition> ( word def -- obj )
    1array <parallel-transition> ;

! This is what quotations are instantiated to, and represent a segment of
! of connected transitions.  These are the things that are passed to combinators
! during stepping
TUPLE: compound-transition entry exit ;
C: <compound-transition> compound-transition

! ** Word-to-transition conversion
PREDICATE: parallel-word < word { [ \ ? eq? ] [ generic? ] } 1|| ;
GENERIC: parallel-defs ( word -- quots )
M: object parallel-defs drop f ;

: single-type-decl ( # type -- quot )
    [ ?? <array> ] [ prefix ] bi* types>declaration ;

: but-not ( classes -- intersection-class )
    object [ class-not class-and ] reduce ;

: compute-single-dispatch ( methods -- methods )
    sort-methods <reversed>
    f swap
    [ [ [ suffix ]
        [ swap but-not class-and ] 2bi ] dip
    ] assoc-map nip
    ;

M: single-generic parallel-defs
    [ "combination" word-prop #>> ]
    [ "methods" word-prop compute-single-dispatch ] bi
    [
        swapd
        [ single-type-decl ]
        [ 1quotation ] bi* compose
    ] with { } assoc>map
    ;

! *** TODO invariant generic double-dispatch
! Actually, the inline definition is already correct.  Rather, any optimization
! is a macro-level transition transformation...
! : insert-math-declarations ( methods -- quots )
!     [| class method |
!      2 class <repetition> types>declaration method 1quotation compose
!     ] { } assoc>map ;

! : compute-math-dispatch ( methods -- methods )
!     compute-single-dispatch
!     insert-math-declarations ;

! M: math-generic parallel-defs
!     "methods" word-prop
!     compute-math-dispatch ;

PREDICATE: non-base < word { if } in? ;

: inline-def? ( word -- ? )
    ! dup class? [ drop f ]
    ! [
        { [ inline? ] ! [ predicate? ]
        [ math-generic? ]
        [ non-base? ] } 1|| ;
    ! ] if ;

! Predicates are type macros in the sense that if we can prove at compile time
! already that it fits, the predicate check can be skipped per definition,
! i.e. without inference at compile-time and without predicate computation at
! runtime.
: predicate-methods ( word -- methods )
    [let
     [ def>> ] [ "predicating" word-prop ] bi :> ( definition class )
     class [ drop t ] 2array 1array
     class superclass-of :> super
     super [
         super class class\ [ drop f ] 2array suffix
         ?? super class\ definition 2array suffix
     ] [
         ?? class class\ definition 2array suffix
     ] if
    ] ;

    ! [ 1array types>configuration [ drop t ] curry ]
    ! [ flatten-class <anonymous-union> 1array types>configuration swap curry ]


    ! [ "predicating" word-prop
    !   [ 1array types>configuration [ drop t ] curry ]
    !   [ flatten-class but-not 1array types>configuration [ drop f ] curry ] bi
    ! ]
    ! [ [ "predicating" word-prop class-not 1array types>configuration ]
    !   [ def>> ] bi curry ] bi 3array ;

M: predicate parallel-defs
    predicate-methods
    [ first2 [ 1array types>declaration ] dip compose ] map
    ;

: <transition> ( word -- obj )
    dup parallel-defs
    [ <parallel-transition> ]
    [ dup inline-def?
      [ dup def>> <inline-transition> ]
      [ <preset-atomic-transition> ] if
    ] if* ;

: <dependent-transition> ( state-in word -- obj )
    swap over type-expand
    [ <inline-transition> ]
    [ <preset-atomic-transition> ] if* ;


! :: connect-transitions ( prev next -- )
!     { [ prev next>> ] [ next prev>> ] } 1||
!     [ "already-connected" throw ] when
!     next prev next<<
!     prev next prev<< ;
    ! [ [ suffix ] curry change-next drop ]
    ! [ [ swap suffix ] change-prev drop ] 2bi ;


! Instantiate and connect straight-line transitions
! Return the entry and exit transitions
! Could already perform input checking here!
: quot>transition ( quot -- compound )
    [ <transition> ] {  } map-as ;
    ! dup 2 <clumps> [ first2 connect-transitions ] each
    ! [ first ] [ last ] bi <compound-transition> ;

SYMBOL: visited
: visited? ( node -- ? )
    visited get in? ;

! * Traversing transition network

:: apply-inputs ( inputs transition -- changed? )
    transition state-in>> :> current-in
    inputs current-in apply-types :> new-in
    current-in new-in = [ f ]
    [ new-in transition state-in<< t ] if ;

:: apply-outputs ( outputs transition -- changed? )
    transition state-out>> :> current-out
    outputs current-out apply-types :> new-out
    current-out new-out = [ f ]
    [ new-out transition state-out<< t ] if ;

! : prev-outputs ( transition -- types )
!     prev>> [ state-out>> ] [ stack-or ] map-reduce ;

GENERIC: apply-transition* ( transition -- transition )
M: transition apply-transition* ( tran -- tran )
    {
        [ state-in>> ]
        [ word>> map-type ]
        [ swap >>state-out ]
    } cleave ;
! Dynamic call transitions that have known inputs get their bodies inlined
! This basically a kind of semi-fold behavior, where only the dispatch is inlined
! NOTE: This is the point where we actually expand the whole code instead of
! performing a nested inference.  For inference only this is overkill, but we
! are interested in compiling out all combinators here...
! Basically this is macro semantics: inline code based on literal arguments.
! Contrast that with foldable computations, which actually replace transitions
! with a different set (a constant push in most cases)
! TODO: trace inlining recursion
: expand-inline-transition ( tran -- tran )
    {
        [ word>> dup def>> <inline-transition> ]
        [ state-in>> >>state-in ]
        [ state-out>> >>state-out ]
        [ id>> >>id ]
    } cleave ;

GENERIC: replace-transition? ( transition -- ? )
GENERIC: replace-transition ( transition -- transition )
M: transition replace-transition? drop f ;
PREDICATE: call-transition < transition word>> \ call eq? ;
M: call-transition replace-transition?
    state-in>> last callable test-literal ;
M: call-transition replace-transition
    {
        [ word>> <wrapper> ]
        [ state-in>> last literal>value
          [ drop ] prepose <inline-transition> ]
        [ state-in>> >>state-in ]
        [ state-out>> >>state-out ]
        [ id>> >>id ]
    } cleave
    ;

: apply-transition ( transition -- transition )
    apply-transition* ;
    ! dup replace-transition?
    ! ! NOTE: recursive macro expansion possible here!
    ! [ replace-transition apply-transition ]
    ! [ apply-transition* ] if ;


GENERIC: revert-transition ( transition -- transition )
M:: transition revert-transition ( tran -- tran )
    tran state-in>> :> current-in
    current-in tran word>> type-inverse :> inverse-quot
    tran state-out>> inverse-quot with-datastack :> new-in
    tran new-in >>state-in ;

! GENERIC: rewind ( tran -- )
! M:: transition rewind ( tran -- )
!     tran revert-transition
!     [ tran prev>> rewind ]
! SINGLETON: +forward+
! SINGLETON: +backward+
! SINGLETON: +stop+
! UNION: direction +forward+ +backward+ +stop+ ;

! :: transition-step ( prev next dir state -- prev next next-dir next-state )
!     { { [ { [ dir +forward+ ] [ next ] [ state next state-in<<  ] } 0&& ] [  ] } }


! Since we only have left-to-right linear connections, we always have a unique
! predecessor and successor.  Thus, we can have cursor semantics, i.e. "sitting"
! on the stack inbetween two transitions .
! We always are on one transition.  Since we have possibly more than one input
! and more than one output, there is no unique predecessor and unique successor
DEFER: ping-pong
DEFER: run-right
SYMBOL: changed
: run-right-with ( state right -- left changed? )
    [ first apply-inputs changed [ or ] change { } ] keep run-right ;
:: apply-parallel-transition ( state transition -- transition )
    transition [ state-in>> ] [ bodies>> ] bi :> ( state-in bodies )
    bodies [
        dup callable? [ quot>transition ] when
        ! dup first state-in >>state-in drop
        ! TODO: pong-ping here with applied inputs!
        [ state swap run-right-with ]
        [ dup declared-null-value? [ 2drop f f ] [ rethrow ] if ]
        recover
        changed [ or ] change
    ] map sift :> traces
    traces empty? [ "no-applicable-method" throw ] when
    traces [ last state-out>> ] [ stack-or ] map-reduce :> state
    transition state >>state-out
    traces >>bodies
    ;

:: left>right ( left next -- next changed? )
    left ?last :> prev
    prev [ state-out>> ] [ { } ] if* :> state
    state next apply-inputs :> changed?
    next dup replace-transition? [ replace-transition ] when
    dup parallel-transition?
    [ state swap apply-parallel-transition ]
    [ apply-transition ] if
    changed? ;

:: left<right ( prev next -- prev changed? )
    next state-in>> :> state
    state prev apply-outputs :> changed?
    prev revert-transition changed? ;

! DEFER: run-right
! DEFER: run-left
DEFER: run-quot-with

:: step-right ( left right -- left right )
    ! left last :> prev
    right unclip :> ( rest next )
    left next left>right :> ( stepped changed? )
    changed [ changed? or ] change
    left stepped suffix rest
    ;

:: step-left ( left right -- left right )
    right first :> next
    left unclip-last :> ( rest prev )
    prev next left<right :> ( stepped changed? )
    changed [ changed? or ] change
    rest right stepped prefix ;

: run-right ( left right -- left changed? )
    f changed [ [ dup empty? ] [ step-right ] until drop changed get ] with-variable ;

: run-left ( left right -- left changed? )
    f changed [ [ over empty? ] [ step-left ] until nip changed get ] with-variable ;

! : ping-pong ( left right -- left )
!     run-right drop
!     1 cut* run-left drop
!     f swap run-right [ "unstable" throw ] when
!     ;

: quot>trace ( quot -- left right )
    quot>transition f swap ;

! : run-quot ( quot -- trace changed? )
!     quot>trace run-right ;
    ! quot>transition f swap ping-pong ;
    ! [ {  } ] [
    !     quot>transition
    !     1 cut
    !     ping-pong ] if-empty ;

! : infer-type ( quot -- effect )
!     run-quot [ first state-in>> ]
!     [ last state-out>> ] bi <type-effect> ;

! : apply-compound ( inputs compound-transition -- compound-transition )

! ** Interleaved with expansion and modular-type-transfer

! Transition sequence elements are either words, or already instantiated
! transition objects, for now, only assume words, e.g. no redo-history keeping
: initial-transition-inputs ( left -- state-in )
    ?last [ state-out>> ] [ H{ } clone ] if* ;

! Possibly recursing
SYMBOL: inline-history


! : step-word ( left word -- transition )
!     [ initial-transition-inputs ] dip
!     2dup type-expand

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

! :: apply-parallel-transfer ( state-in cases -- state-out )
: apply-parallel-transfer ( state-in cases -- state-out )
    dupd [ infer-branch-transfer 2array ] with map
    unzip
    [ [ <flipped> [ squish-type-values ] map ] keep ] dip
    [ all-parallel>merge current-transfer [ swap compose-transfers ] change ]
    [ all-parallel<merge current-undo [ swap prepose-transfers ] change ]
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
! compiled type quotations to verify the same result holds
: ping-pong-ping ( quot -- in out2 out1 )
    ping-pong [ swap dupd transfer-quots>> apply-transfers ] dip ;
