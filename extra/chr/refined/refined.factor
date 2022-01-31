USING: accessors arrays assocs assocs.extras byte-arrays chr classes.tuple
combinators.short-circuit hash-sets kernel match math math.order namespaces
prettyprint quotations sequences sequences.extras sets sorting strings typed
types.util words ;

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
!   constraints whose args might be affected
! - Fixed constraints are not reactivated
!   - Fixed: additional built-in constraint cannot alter entailment of guards on
!     these arguments
!   - -> Only wake CHR constraints whose variables are further constraint by newly
!     added constraint
!   - A variable which can only take one value to satisfy B is fixed
!     - constraint c is fixed if vars(c) ⊆ fixed(B)


! - Traversal: active constraint tries its occurrences in top-down right-to-left order
! - Activating or Reactivating /occurrenced/ constraints
! - occurrenced identified constraints c#i:j : only matches with j'th occurrence
!   of constraint c are considered when constraint is active.
!   - For each constraint type, an index is computed to steer match attempts

! - Each active constraint traverses its different occurrences
!   via the Default transitions, finally being Dropped

! Interaction with builtin solver:
! - /telling/: Provide substitution, new constraint added to CHR store
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

: read-chr ( rules -- chr-prog )
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
M: object child-atoms drop { } ;
M: word child-atoms drop f ;
M: string child-atoms drop { } ;
M: byte-array child-atoms drop { } ;
M: sequence child-atoms ;
M: tuple child-atoms tuple-slots ;
M: eq child-atoms [ v1>> ] [ v2>> ] bi 2array ;
M: match-var child-atoms drop f ;
! M: id-cons child-atoms constraint-args ;

: atoms ( obj -- seq )
    [ child-atoms ] [ drop t ] deep-find-all ;

TYPED: store-atoms ( c: chr-cons -- c: chr-cons )
    dup cons>> constraint-args atoms >>atoms ;

: wrap-cons ( obj -- constraint )
    dup builtin-constraint?
    [ f <builtin-cons> ]
    [ f <chr-cons> ] if ;

: init-chr-state ( rules query -- )
    reset-chr-state
    [ wrap-cons ] map exec-stack set
    read-chr program set ;

! * Transitions
TYPED: identify-cons ( c: chr-cons -- c: id-cons )
    store-atoms current-index [ 0 or 1 + dup ] change
    <id-cons> ;

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
GENERIC: tell ( cons -- subst store )

M: eq tell
    [ [ v1>> ] [ v2>> ] bi 2array 1array ] keep ;
M: set-eq tell
    [ v1>> ] [ v2>> ] bi call( -- val ) <eq> tell drop f ;

M: generator tell
    [ body>> ]
    [ vars>> [ dup dup word? [ name>> ] when uvar <gvar> ] H{ } map>assoc ] bi lift
    [ wrap-cons ] map
    exec-stack [ append ] change f f ;

M: callable tell
    call( -- builtin-res ) f swap ;

: standard-wakeup-set ( subst -- ids )
    values
    store get [ cons>> atoms>> intersects? ] with find-all [ second ] <mapped> ;

! TODO
TYPED:: solve-builtin ( c: builtin-cons -- )
    c cons>> tell :> ( subst to-store )
    { exec-stack store builtins }
    [ [ subst lift ] change ] each
    subst standard-wakeup-set :> to-wakeup
    exec-stack get :> estack
    to-wakeup members [ estack [ dup active-cons? [ cons>> ] when ] <mapped> member? ] reject
    exec-stack [ append ] change
    to-store [ ! f <builtin-cons>
               builtins [ swap suffix ] change ] when* ;

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

! Hs: pairs of index, head
! inds: pairs of { head-index E-index }
:: find-heads-index ( Hs E without-E subst! -- subst inds )
    Hs [ subst f ]
    [ unclip-slice :> ( r hind )
      hind first2 :> ( hi h )
      E [| H i | i without-E in? [ f ]
         [ subst h H 2array 1array solve-next [ subst! t ] [ f ] if* ] if
        ] find-index :> ( i h2 )
      i [ r E without-E i suffix subst find-heads-index { hi i } suffix ] [ f f ] if
    ] if-empty ;

TYPED:: try-simpligate ( c: active-cons -- ir add propagate? ? )
    c cons>> :> idc
    idc cons>> cons>> :> hc
    c [ j>> ] [ occs>> ] bi nth first2
    [ program get rules>> nth ] dip :> ( H rj )
    store get :> S
    idc S index :> i_act
    S [ cons>> cons>> ] <mapped> :> E
    hc rj H heads>> nth solve-eq :> subst
    rj H heads>> <enumerated> remove-nth :> H1
    H1 E i_act 1array subst find-heads-index :> ( sh ih_pairs )
    H ih_pairs values [ S nth id>> ] map >hash-set [ rj swap adjoin ] keep 2array :> tsig
    H nkept>> :> nk
    nk H heads>> length = :> prop?
      { [ sh ]
        [ { [ prop? ] [ tsig match-trace get in? ] } 0&& not ]
      } 0&&
      [
          H guard>> [ sh lift builtin-applies? ] all? [
              ih_pairs [ nk >= ] filter-keys values [ S nth id>> ] map :> ir
              ! ir: indices in s to remove
              H body>> dup t = [ drop f ] [ [ sh lift wrap-cons ] map ] if :> add
              prop? [ match-trace [ tsig suffix ] change ] when
              rj nk < ! true: propagate false: simplify
              [ ir add t ]
              [ ir idc id>> suffix add f ] if
              t
          ] [ f f f f ] if
      ] [ f f f f ] if
    ;

TYPED: simpligate ( c: active-cons -- ? )
    dup dup occs>> empty? [ 2drop f ]
    [ try-simpligate
      [| c ir add prop? |
       prop? [ c push-cons ] when
       exec-stack [ add prepend ] change
       store [ [ id>> ir in? ] reject ] change
       t ]
      [ 4drop f ] if ] if ;

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
      [ simpligate ]
      [ default/drop ]
    } 1|| ] if ;

SYMBOL: chr-state-sentinel

: chr-loop ( -- state )
    [ 0 chr-state-sentinel set
      [ chr-state-sentinel get 500 > [ "runaway" throw ] when
        chr-state-sentinel inc
        chr-trans
        ! chr.
      ] loop
      get-chr-state
    ] with-scope ;

: chr-run-refined ( rules query -- store builtins )
    [ init-chr-state chr-loop
      [ store of [ cons>> cons>> ] map ]
      [ builtins of ! [ cons>> ] map
      ] bi
    ] with-var-names ;

! * Debug
SYMBOL: saved-state
: save-chr ( -- )
    program get
    get-chr-state 2array saved-state set ;

: load-chr ( -- )
    saved-state get
    first2 [ swap set ] assoc-each
    program set ;
