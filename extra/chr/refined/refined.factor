USING: accessors arrays assocs assocs.extras byte-arrays chr chr.debug chr.state
classes.tuple combinators.short-circuit hash-sets kernel match math math.order
namespaces prettyprint quotations sequences sequences.extras sets sorting
strings typed types.util words ;

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


TUPLE: chr-prog rules occur-index var-index ;
C: <chr-prog> chr-prog

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

! For adding things to the exec stack
GENERIC: child-atoms ( obj -- seq/f )
M: object child-atoms drop { } ;
M: word child-atoms drop f ;
M: string child-atoms drop { } ;
M: byte-array child-atoms drop { } ;
M: sequence child-atoms ;
M: tuple child-atoms tuple-slots ;
M: binary-constraint child-atoms [ v1>> ] [ v2>> ] bi 2array ;
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

M: binary-constraint tell f swap ;

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

! Check if the builtin is trivial.  This is convenience
GENERIC: keep-guard? ( builtin-cons -- ? )
M: eq keep-guard? [ v1>> ] [ v2>> ] bi = not ;
! Don't keep around callables per default.  If these are supposed to be part of
! protocol, then create a custom constraint in the theory!
M: callable keep-guard? drop f ;
M: object keep-guard? drop t ;
M: binary-constraint keep-guard?
    [ v1>> ] [ v2>> ] bi [ number? ] both? not ;

GENERIC: wake-up-set ( cons -- atoms )
M: object wake-up-set drop f ;
M: binary-constraint wake-up-set atoms ;
: calculate-wakeup-set ( subst cons -- ids )
    [ values ] [ wake-up-set ] bi* append
    store get [ cons>> atoms>> intersects? ] with find-all [ second ] <mapped> ;

! TODO: formalize constraint building/substitution/args/reconstruction protocol!
GENERIC#: lift-cons 1 ( cons subst -- cons )
M: sequence lift-cons
    [ lift-cons ] curry map ;
M: active-cons lift-cons
    [ lift-cons ] curry change-cons ;
M: id-cons lift-cons
    [ lift-cons ] curry change-cons ;
! NOTE: changing atoms along!
M: chr-cons lift-cons lift ;
M: builtin-cons lift-cons lift ;
M: binary-constraint lift-cons lift ;

TYPED:: solve-builtin ( c: builtin-cons -- )
    c cons>> tell :> ( subst c2 )
    c2 keep-guard? [ c2 ] [ f ] if :> to-store
    { exec-stack store builtins }
    [ [ subst lift-cons ] change ] each
    subst c2 calculate-wakeup-set :> to-wakeup
    exec-stack get :> estack
    to-wakeup members [ estack [ dup active-cons? [ cons>> ] when ] <mapped> member? ] reject
    exec-stack [ append ] change
    to-store [ dup builtins get in?
               [ drop ]
               [ builtins [ swap suffix ] change ] if
     ] when*

    ! debug
    "solve" f "wake" to-wakeup [ id>> ] map 2array { "told" to-store } suffix
    log-chr

    ;

: solve ( cons -- ? )
    dup builtin-cons?
    [ solve-builtin t ]
    [ drop f ] if ;

GENERIC: activate* ( cons -- ? )
M: object activate* drop f ;
M: chr-cons activate*
    identify-cons
    ! TODO: or suffix?
    store [ over prefix ] change
    activate* ;
M: id-cons activate* activate-cons push-cons t ;

:: activate ( c -- ? )
    c activate* dup
    [ c chr-cons?
      [ "activate" f store get first id>> ]
      [ "reactivate" f c id>> ] if
      log-chr ] when ;

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

TYPED: deref-occurrence ( c: active-cons -- i_rule rj )
    [ j>> ] [ occs>> ] bi nth first2 ;

TYPED:: try-simpligate ( c: active-cons -- ir add propagate? ? )
    c cons>> :> idc
    idc cons>> cons>> :> hc
    c deref-occurrence
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
          H guard>> [ sh lift ] map :> B1
          B1 [ builtin-applies? ] all? [
              ih_pairs [ nk >= ] filter-keys values [ S nth id>> ] map :> ir
              ! ir: indices in s to remove
              H body>> dup t = [ drop f ] [ [ sh lift wrap-cons ] map ] if :> add
              prop? [ match-trace [ tsig suffix ] change ] when
              rj nk < ! true: propagate false: simplify
              [ ir add t ]
              [ ir idc id>> suffix add f ] if
              t
              ! Note: modifying state here already!
              builtins [ B1 [ keep-guard? ] filter append ] change
          ] [ f f f f ] if
      ] [ f f f f ] if
    ;

TYPED: simpligate ( c: active-cons -- ? )
    dup dup occs>> empty? [ 2drop f ]
    [ try-simpligate
      [| c ir add prop? |
       prop? [ c push-cons ] when
       exec-stack [ add prepend ] change
       ! store get [ id>> ir in? ] filter :> rem ! Only for debugging!
       ! store get <enumerated> [ id>> ir in? ] filter-values :> rem ! Only for debugging!
       store [ [ id>> ir in? ] reject ] change
       t

       ! Add log-entry TODO make conditional on flag
       c deref-occurrence :> ( i_rule rj )
       i_rule program get rules>> nth :> rule
       prop? "propagate" "simplify" ? rule named-chr? [ rule rule-name>> ] [ i_rule ] if rj 2array
       { { "remove" ir } { "add" add } } log-chr

      ]
      [ 4drop f ] if ] if ;

TYPED:: default/drop ( ac: active-cons -- ? )
    ac j>> 1 + :> j2
    ac occs>> :> occs
    occs length :> njs
    j2 njs >= dup :> drop?
    [ ac cons>> occs j2 <active-cons> push-cons ] unless
    t

    drop? "drop" "default" ? f j2 log-chr
    ;

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
        debug-chr? [ chr. ] when
      ] loop
      ! FIXME: there should probably be a better point to check when builtin
      ! guards are to be kept! Need to keep track of modification in guard store
      ! for that when applying substitutions
      builtins [ [ keep-guard? ] filter members ] change
      get-chr-state
    ] with-scope ;

: chr-run-refined ( rules query -- store builtins )
    [ init-chr-state chr-loop
      [ store of [ cons>> cons>> ] map ]
      [ builtins of ] bi
    ] with-var-names ;


: do-chr ( program query -- store builtins )
    over .
    debug-chr [
        chr-run-refined
        2dup [ . ] bi@
    ] with-variable-on ;
