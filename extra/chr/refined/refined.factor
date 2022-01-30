USING: accessors arrays assocs assocs.extras byte-arrays chr classes.tuple
combinators.short-circuit hash-sets kernel match math math.order namespaces
prettyprint sequences sequences.extras sets sorting strings typed types.util
words ;

IN: chr.refined

FROM: namespaces => set ;

! * Semantics

! - Queries and bodies are executed left-to-right
! - When CHR is executed, it becomes active
! - Looks for matching rules top-to-bottom
! - If rule fires, constraints in body become active first
! - After handling those, control returns to formerly active constraint

! Execution State:
! Stack A, store S, builtin store B, Propagation History T, n, Var

! A is exec stack
! S can hold identified constraints that can be matched with the rules.
! B logical conjunction of builtin-constraints
! n next free constraint identifier
! Var: Set of free variables present in the query

! - Active constraint is top-most on stack
! - Activate transition: initiates sequence of searches for partner constraints to
!   match rule heads.
! - Adding built-in initiates similar searches for rules, causes Reactivate to all
!   constraints whose args might be effected???
! - Fixed constraints are not reactivated ???
!   - Fixed: additional built-in constraint cannot alter entailment of guards on
!     these arguments
!   - -> Only wake CHR constraints whose variables are further constraint by newly
!     added constraint
!   - A variable which can only take one value to satisfy B is fixed
!     - constraint c fixed if vars(c) ⊆ fixed(B) ???


! - Traversal: active constraint tries its occurrences in top-down right-to-left order
! - Activating or Reactivating /occurrences/ constraints???
! - occurrenced identified constraints c#i:j : only matches with j'th occurrence
!   of constraint c are considered when constraint is active....???

! - Each active constraint traverses its different occurrences (how can that be?)
!   via the Default transitions, finally being Dropped

! Interaction with builtin solver:
! - /telling/: New constraints added to CHR store
! - /asking/: Check entailments in guards
! - Alert CHR handlers when changes in builtin constraint store might cause
!   (previously failing) entailment tests to succeed.


! Internal form in program
TUPLE: chr-cons cons atoms ;
C: <chr-cons> chr-cons

TUPLE: builtin-cons cons atoms ;
C: <builtin-cons> builtin-cons

TUPLE: id-cons { cons maybe{ chr-cons } } id ;
C: <id-cons> id-cons
TUPLE: active-cons { cons maybe{ id-cons } } occs j ;
C: <active-cons> active-cons

TUPLE: chr-prog rules occur-index var-index ;
C: <chr-prog> chr-prog
! TUPLE: susp type args id alive? activated? stored? ;
! TUPLE: store n ;

TUPLE: chr-state stack store builtins trace n vars ;

! Needs to be implemented by non-builtins
GENERIC: constraint-type ( obj -- type )
GENERIC: constraint-args ( obj -- args )
PREDICATE: pred-seq < sequence first word? ;
M: pred-seq constraint-type first ;
M: pred-seq constraint-args rest-slice ;
M: chr-cons constraint-type cons>> constraint-type ;
M: id-cons constraint-type cons>> constraint-type ;
M: chr-cons constraint-args cons>> constraint-args ;
M: id-cons constraint-args cons>> constraint-args ;

: sort-chr-index ( coords -- cords )
    [ 2dup [ first ] bi@ <=> dup +eq+ =
      [ drop [ second ] bi@ >=< ]
      [ 2nip ] if
    ] sort ;

: index-rules ( chrs -- index )
    H{ } clone swap
    [ swap heads>>
      [ rot dup builtin-constraint? [ 3drop ]
        [
            [ 2array ] dip constraint-type pick push-at
        ] if
      ] with each-index
    ] each-index
    [ sort-chr-index >array ] map-values ;

! : wrap-rule-constraints ( rules -- rules )
!     [ clone
!       [ [ wrap-cons ] map ] change-heads
!       [ dup t = [ [ wrap-cons ] map ] unless ] change-body
!     ] map ;

: read-chr ( rules -- chr-prog )
    ! dup wrap-rule-constraints
    dup index-rules f <chr-prog> ;

SYMBOLS: program exec-stack store builtins match-trace current-index ;

: reset-chr-state ( -- )
    exec-stack off
    store off
    builtins off
    match-trace off
    0 current-index set ;

: with-new-chr-state ( quot -- )
    [ reset-chr-state ] prepose with-scope ; inline

: get-chr-state ( -- assoc )
    { exec-stack store builtins match-trace current-index }
    [ dup get ] H{ } map>assoc ;

: chr. ( -- )
    program get .
    get-chr-state . ;


! For adding things to the exec stack
GENERIC: child-atoms ( obj -- seq/f )
M: object child-atoms drop f ;
M: string child-atoms drop f ;
M: byte-array child-atoms drop f ;
M: sequence child-atoms ;
M: tuple child-atoms tuple-slots ;
M: eq child-atoms [ v1>> ] [ v2>> ] bi 2array ;
! M: id-cons child-atoms constraint-args ;

: atoms ( obj -- seq )
    [ child-atoms ] [ match-var? not ] deep-find-all ;

: wrap-cons ( obj -- constraint )
    dup builtin-constraint?
    [ dup atoms <builtin-cons> ]
    [ dup constraint-args atoms <chr-cons> ] if ;

: init-chr-state ( rules query -- )
    reset-chr-state
    [ wrap-cons ] map exec-stack set
    read-chr program set ;

! * Transitions
TYPED: identify-cons ( c: chr-cons -- c: id-cons )
    current-index [ 0 or 1 + dup ] change <id-cons> ;

TYPED: activate-cons ( c: id-cons -- c: active-cons )
    dup cons>> constraint-type program get occur-index>> at 0
    <active-cons> ;

: push-cons ( cons -- )
    exec-stack [ swap prefix ] change ;

: peek-cons ( -- x )
    exec-stack get first ;

: ?pop-cons ( -- cons ? )
    exec-stack get
    [ f f ]
    [ exec-stack [ dup rest ] change ]
    if-empty ;

! Run builtin. Interface is telling renamings and waking corresponding constraints.
GENERIC: tell ( cons -- subst )

M: eq tell
    [ v1>> ] [ v2>> ] bi 2array 1array ;

! :: standard-wakeup-set ( atoms -- ids )
!     [ store get [| c | c cons>> atoms>> atoms intersect? [ c , ] when ]
!       each ] { } make ;
: standard-wakeup-set ( atoms -- ids )
    store get [ cons>> atoms>> intersects? ] with find-all [ second ] <mapped> ;

! TODO
TYPED:: solve-builtin ( c: builtin-cons -- )
    ! break
    c cons>> tell :> subst
    { exec-stack store builtins }
    [ [ subst lift ] change ] each
    c atoms>> standard-wakeup-set :> to-wakeup
    exec-stack get :> estack
    to-wakeup members [ estack [ dup active-cons? [ cons>> ] when ] <mapped> member? ] reject
    exec-stack [ append ] change
    builtins [ c suffix ] change ;

: solve ( cons -- ? )
    dup builtin-cons?
    [ solve-builtin t ]
    [ drop f ] if ;

: maybe-activate-cons ( cons -- ? )
    dup id-cons?
    [ activate-cons push-cons t ]
    [ drop f ] if ;

GENERIC: activate ( cons -- ? )
M: object activate drop f ;
M: chr-cons activate
    identify-cons
    ! TODO: or suffix?
    store [ over prefix ] change
    activate ;
M: id-cons activate activate-cons push-cons t ;

! : activate ( c: cons -- ? )
!     activate ;

! : reactivate ( c: -- ? )
!     peek-cons maybe-activate-cons ;

! :: wrap-builtin-backref ( b subst -- cons )
!     subst values :> touches
!     b subst lift touches <builtin-cons> ;

TYPED:: try-simpligate ( c: active-cons -- ir add propagate? ? )
    ! break
    c cons>> :> idc
    idc cons>> cons>> :> hc
    c [ j>> ] [ occs>> ] bi nth first2
    [ program get rules>> nth ] dip :> ( H rj )
    idc store get remove :> S
    S [ cons>> cons>> ] <mapped> :> E
    hc rj H heads>> nth solve-eq :> subst
    rj H heads>> remove-nth :> H1
    H1 E f subst find-heads :> ( sh ih )
    H ih [ S nth id>> ] map >hash-set [ rj swap adjoin ] keep 2array :> tsig
    ! { [ sk ] [ H keep>> empty? ] } 0||
    ! [ H remove>> E ik sk find-heads :> ( sr ir )
    H nkept>> :> nk
    nk H heads>> length = :> prop?
      { [ sh ]
        [ { [ prop? ] [ tsig match-trace get in? ] } 0&& not ]
      } 0&&
      [
          H guard>> [ sh lift builtin-applies? ] all? [
              ih [ nk >= ] filter :> ir
              H body>> dup t = [ drop f ] [ [ sh lift wrap-cons ] map ] if :> add
              prop? [ match-trace [ tsig suffix ] change ] when
              rj nk < ! true: propagate false: simplify
              [ ir add t ]
              [ ir idc id>> suffix add f ] if
              t
          ] [ f f f f ] if
      ] [ f f f f ] if ! ]
    ! [ E f ] if
    ;

TYPED: simpligate ( c: active-cons -- ? )
    dup try-simpligate
    [| c ir add prop? |
     ! break
     prop? [ c push-cons ] when
     exec-stack [ add prepend ] change
     store [ [ id>> ir in? ] reject ] change
     t
    ]
    [ 4drop f ] if ;

TYPED:: default/drop ( ac: active-cons -- ? )
    ac j>> 1 + :> j2
    ac occs>> :> occs
    occs length :> njs
    j2 njs >=
    [ ac cons>> occs j2 <active-cons> push-cons ] unless
    t ;


: chr-trans ( -- ? )
    exec-stack get empty?
    [ f ]
    [ exec-stack [ unclip-slice swap ] change
    { [ solve ]
      [ activate ]
      ! [ reactivate ]
      [ simpligate ]
      [ default/drop ]
    } 1|| ] if ;

SYMBOL: chr-state-sentinel

: chr-loop ( -- state )
    [ 0 chr-state-sentinel set
      [ chr-state-sentinel get 50 > [ "runaway" throw ] when
        chr-state-sentinel inc
        chr-trans
        ! chr.
      ] loop
      get-chr-state
    ] with-scope ;

: chr-run-refined ( rules query -- store builtins )
    [ init-chr-state chr-loop
      [ store of [ cons>> cons>> ] map ]
      [ builtins of [ cons>> ] map ] bi
    ] with-scope ;

! * Debug
SYMBOL: saved-state
: save-chr ( -- )
    program get
    get-chr-state 2array saved-state set ;

: load-chr ( -- )
    saved-state get
    first2 [ swap set ] assoc-each
    program set ;
