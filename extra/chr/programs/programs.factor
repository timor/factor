USING: accessors arrays assocs assocs.extras chr chr.factor chr.modular kernel
math math.order sequences sets sorting terms types.util ;

IN: chr.programs


! Program itself
TUPLE: chr-prog
    rules
    occur-index
    schedule
    local-vars
    existential-vars ;

C: <chr-prog> chr-prog

TUPLE: constraint-schedule
    { occurrence read-only }
    { keep-active? read-only }
    { arg-vars read-only }
    { partners read-only }
    { rule-vars read-only } ;
C: <constraint-schedule> constraint-schedule

! * Rule processing
: sort-chr-index ( coords -- cords )
    [ 2dup [ first ] bi@ <=> dup +eq+ =
      [ drop [ second ] bi@ >=< ]
      [ 2nip ] if
    ] sort ;

: index-rules ( chrs -- index )
    H{ } clone swap
    [ swap heads>>
      [ rot [ 2array ] dip constraint-type pick push-at ] with each-index
    ] each-index
    [ sort-chr-index >array ] map-values ;

! Return an assoc of schedules per constraint type, which are sequences of
! { occ keep-active { keep-partner partner-type } } entries
: make-schedule ( rules occur-index -- schedule )
    [| rules occs |
     occs
     [ dup first2 [ rules nth ] dip :> ( rule occ-hi )
         rule nkept>> :> nk
         occ-hi nk <
         occ-hi rule heads>> nth constraint-args
         V{ } clone
         rule heads>> [| c i | i occ-hi = not [ i nk < c 2array suffix! ] when ] each-index
         >array
         rule match-vars>>
         <constraint-schedule>
      ] map
    ] with assoc-map ;

: collect-vars ( rules -- set )
    ! vars { +top+ +end+ } diff members
    ! vars +top+ swap remove-eq +end+ swap remove-eq members
    term-vars
    ;

ERROR: existential-guard-vars rule ;
:: rule-existentials ( rule -- set )
    rule
    [ heads>> collect-vars ]
    [ guard>> collect-vars ]
    [ body>> collect-vars  ] tri :> ( vh vg vb )
    vb vh diff :> existentials
    vg members [ vh in? not ] any? [ rule existential-guard-vars ] when
    existentials
    ;

: collect-existential-vars ( rules -- seq )
    [ rule-existentials ] map ;


: read-chr ( rules -- rules )
    [ internalize-rule ] map ;

! NOTE: destructive!
! FIXME: may be better to do that stuff per rule, not per program?
: insert-generators! ( rule vars -- rule )
    [
        '[ _ swap <generator> 1array ] change-body
    ] unless-empty ;

! Destructive!
: convert-existentials! ( chr-prog -- chr-prog )
    dup [ rules>> ] [ existential-vars>> ] bi
    [ insert-generators! ] 2map >>rules ;

: check-body-constraint-effect ( effect -- ? )
    { [ terminated?>> ] [ ( -- new ) effect= ] } 1|| ;

ERROR: wrong-builtin-effect quot effect ;
: check-body-quots ( rules -- )
    [ body>> [
          dup callable?
          [ dup infer dup check-body-constraint-effect
            [ 2drop ]
            [ wrong-builtin-effect ] if
          ] [ drop ] if
      ] each ] each ;

: load-chr ( rules -- chr-prog )
    read-chr
    dup check-body-quots
    rewrite-chrat-prog
    dup index-rules
    2dup make-schedule
    pick
    [ collect-vars ]
    [ collect-existential-vars ] bi
    <chr-prog>
    convert-existentials! ;

: rule-depends-on-preds ( rule -- words )
    guard>> [ chrat-pred? ] filter [ constraint-type ] map members ;

: rules-depend-on-preds ( rules -- words )
    [ rule-depends-on-preds ] gather ;

: pred-depends-on-solvers ( pred -- seq )
    pred>chrat-definer [ chrat-solver-deps ] keep prefix ;

: solver-depends-on-preds ( word -- seq )
    chrat-solver-rules [ rule-depends-on-preds ] gather ;

: solvers-depend-on-preds ( seq -- seq )
    [ solver-depends-on-preds ] gather ;

: pred-depends-on-rules ( word -- seq )
    dup chrat-pred-class? [ pred>chrat-definer [ chrat-solver-rules ] [ chrat-solver-deps ] bi append ] [ drop f ] if ;

: collect-chrat-solvers ( constraints -- solvers )
    [ chrat-pred? ] filter [ constraint-type pred-depends-on-solvers ] gather
    [
        solver-depends-on-preds
        [ pred-depends-on-solvers ] gather
    ] V{ } forest-as ;

: collect-chrat-rules ( constraints -- rules )
    collect-chrat-solvers <reversed> [ chrat-solver-rules ] gather ;

: prepare-query ( query -- program query )
    [ pred>constraint ] map [ collect-chrat-rules ] keep ;
