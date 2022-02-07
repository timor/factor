USING: accessors arrays assocs assocs.extras chr chr.modular classes kernel math
math.order sequences sets sorting types.util words ;

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
    { partners read-only } ;
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
         <constraint-schedule>
      ] map
    ] with assoc-map ;

: collect-vars ( rules -- set )
    vars members ;

ERROR: existential-guard-vars rule ;
:: rule-existentials ( rule -- set )
    rule
    [ heads>> vars ]
    [ guard>> vars ]
    [ body>> vars  ] tri :> ( vh vg vb )
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

: load-chr ( rules -- chr-prog )
    read-chr
    rewrite-chrat-prog
    dup index-rules
    2dup make-schedule
    pick
    [ collect-vars ]
    [ collect-existential-vars ] bi
    <chr-prog>
    convert-existentials! ;

: rule-depends-on-preds ( rule -- seq )
    guard>> [ chrat-pred? ] filter [ class-of ] map members ;

: rules-depend-on-preds ( rules -- seq )
    [ rule-depends-on-preds ] gather ;

: pred-depends-on-rules ( pred -- seq )
    dup chrat-pred? [ class-of "chrat-prog" word-prop ] [ drop f ] if ;

: collect-chrat-rules ( constraints -- rules )
    [ chrat-pred? ] filter [ pred-depends-on-rules
                             rules-depend-on-preds
    ] V{ } forest-as
    [ class-of "chrat-prog" word-prop ] gather ;

: prepare-query ( query -- program query )
    [ pred>constraint ] map [ collect-chrat-rules ] keep ;
