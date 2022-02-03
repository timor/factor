USING: accessors arrays assocs assocs.extras classes classes.algebra
classes.tuple combinators.short-circuit continuations kernel make match math
math.order quotations sequences sets sorting typed types.util words ;

IN: chr

FROM: namespaces => set ;

! * Constraint Handling Rules


TUPLE: chr heads nkept guard body ;
: new-chr ( heads nkept guard body class -- obj )
    new
    swap >>body
    swap >>guard
    swap >>nkept
    swap >>heads ;

TUPLE: named-chr < chr rule-name ;
: <named-chr> ( name heads nkept guard body -- obj )
    named-chr new-chr swap >>rule-name ;

: keep/remove ( chr -- seq seq )
    [ heads>> ] [ nkept>> ] bi cut-slice ; inline

! Internal Constraints form in program
TUPLE: chr-cons cons atoms ;
C: <chr-cons> chr-cons

TUPLE: builtin-cons cons atoms ;
C: <builtin-cons> builtin-cons

TUPLE: id-cons { cons maybe{ chr-cons } } id ;
C: <id-cons> id-cons
TUPLE: active-cons { cons maybe{ id-cons } } occs j ;
C: <active-cons> active-cons

! Generated variable.  Not a match-var, but a child-atom to consider
! TODO: make identity-tuple?
TUPLE: gvar { name read-only } ;
C: <gvar> gvar
! M: gvar child-atoms drop f ;
M: gvar subst var-subst ;
M: gvar vars* , ;

MIXIN: chr-constraint
SINGLETON: true
INSTANCE: true chr-constraint

TUPLE: chr-pred ;
INSTANCE: chr-pred chr-constraint

! Turn lexical representation into constraint object
GENERIC: pred>constraint ( obj -- chr-pred )
M: chr-constraint pred>constraint ;

! Simplest representation
PREDICATE: pred-head-word < word chr-pred class<= ;
PREDICATE: pred-array < array ?first pred-head-word? ;
PREDICATE: fiat-pred-array < array ?first { [ word? ] [ pred-head-word? not ] } 1&& ;
INSTANCE: fiat-pred-array chr-constraint

M: pred-array pred>constraint
    unclip-slice slots>tuple ;

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

GENERIC: constraint-type ( obj -- type )
GENERIC: constraint-args ( obj -- args )

M: chr-pred constraint-type class-of ;
M: chr-pred constraint-args tuple-slots ;
M: fiat-pred-array constraint-type first ;
M: fiat-pred-array constraint-args rest-slice ;

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

TYPED: internalize-constraint ( lexical-rep -- c: chr-constraint )
    pred>constraint ; inline

: internalize-constraints ( seq -- seq )
    dup t = [ [ internalize-constraint ] map ] unless ;

: internalize-rule ( chr-rule -- chr-rule )
    clone
    [ internalize-constraints ] change-heads
    [ internalize-constraints ] change-guard
    [ internalize-constraints ] change-body ;

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

: load-chr ( rules -- chr-prog )
    read-chr dup index-rules
    2dup make-schedule
    pick
    [ collect-vars ]
    [ collect-existential-vars ] bi
    <chr-prog> ;

UNION: chr-atom match-var ;
GENERIC: atoms* ( obj -- )
: atoms ( obj -- seq )
    [ atoms* ] { } make ;
M: object atoms* drop ;
M: chr-atom atoms* , ;
M: array atoms* [ atoms* ] each ;
M: tuple atoms* tuple-slots atoms* ;
M: chr-constraint atoms*
    constraint-args atoms* ;

! ! For adding things to the exec stack
! GENERIC: child-atoms ( obj -- seq/f )
! M: object child-atoms drop { } ;
! M: word child-atoms drop f ;
! M: string child-atoms drop { } ;
! M: byte-array child-atoms drop { } ;
! M: sequence child-atoms ;
! M: tuple child-atoms tuple-slots ;
! M: match-var child-atoms drop f ;
! ! NOTE: this is important for nesting!!!
! M: chr-constraint child-atoms constraint-args ;

! : atoms ( obj -- seq )
!     [ child-atoms ] [ drop t ] deep-find-all ;

! Wakeup set
GENERIC: wake-up-set ( constraint -- atoms )
M: chr-constraint wake-up-set atoms ;

! Called on constraints in ask position
GENERIC: test-constraint ( bindings chr -- ? )
! TODO move this to activation!
GENERIC: constraint-fixed? ( chr-constraint -- ? )
M: chr-constraint constraint-fixed? constraint-args atoms empty? ;

GENERIC: apply-substitution* ( subst chr-constraint -- chr-constraint )
M: true apply-substitution* nip ;
M: chr-pred apply-substitution*
    [ tuple-slots swap lift ]
    [ class-of ] bi slots>tuple ;
! M: fiat-pred-array apply-substitution*
!     unclip-slice [ swap lift ] dip prefix ;

! * Arbitrary guards
INSTANCE: callable chr-constraint
M: callable apply-substitution* swap lift ;
: test-callable ( callable -- ? )
    [ call( -- ? ) ] [ 2drop f ] recover ;

M: callable test-constraint
    swap lift test-callable ;

! * Existential callout
TUPLE: generator vars body ;
C: <generator> generator
INSTANCE: generator chr-constraint
M: generator pred>constraint
    clone [ [ pred>constraint ] map ] change-body ;
M: generator apply-substitution*
    clone [ [ apply-substitution* ] with map ] change-body ;
