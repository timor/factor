USING: accessors arrays assocs assocs.extras byte-arrays classes classes.algebra
classes.tuple combinators combinators.short-circuit continuations formatting
kernel logic logic.private match math math.order namespaces quotations sequences
sets sorting strings typed types.util words ;

IN: chr

FROM: namespaces => set ;

! * Constraint Handling Rules

! Constraint store: Sequence of constraints denoting a conjunction
! ⟨F,E,D⟩ where F: Goal Store, D, E, accumulator/simplifier Store


TUPLE: generator vars body ;
C: <generator> generator

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
TUPLE: gvar { name read-only } ;
C: <gvar> gvar
! M: gvar child-atoms drop f ;
M: gvar subst var-subst ;

MIXIN: chr-constraint

TUPLE: chr-pred ;
INSTANCE: chr-pred chr-constraint

! Turn lexical representation into constraint object
GENERIC: pred>constraint ( obj -- chr-pred )
M: chr-constraint pred>constraint ;

! Simplest representation
PREDICATE: pred-head-word < word chr-pred class<= ;
PREDICATE: pred-array < array ?first pred-head-word? ;
PREDICATE: fiat-pred-array < array ?first "chr-pred-head" word-prop? ;
\ = t "chr-pred-head" set-word-prop
INSTANCE: fiat-pred-array chr-constraint

M: pred-array pred>constraint
    unclip-slice slots>tuple ;

! Program itself
TUPLE: chr-prog rules occur-index schedule ;
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
    ! [ rules>> ] [ occur-index>> ] bi
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

: read-chr ( rules -- chr-prog )
    [ internalize-rule ] map dup index-rules
    2dup make-schedule <chr-prog> ;


! For adding things to the exec stack
GENERIC: child-atoms ( obj -- seq/f )
M: object child-atoms drop { } ;
M: word child-atoms drop f ;
M: string child-atoms drop { } ;
M: byte-array child-atoms drop { } ;
M: sequence child-atoms ;
M: tuple child-atoms tuple-slots ;
M: match-var child-atoms drop f ;
! NOTE: this is important for nesting!!!
M: chr-constraint child-atoms constraint-args ;

: atoms ( obj -- seq )
    [ child-atoms ] [ drop t ] deep-find-all ;

! Wakeup set
GENERIC: wake-up-set ( constraint -- atoms )
M: chr-constraint wake-up-set atoms ;


GENERIC: match-constraint ( bindings store-args chr -- bindings )
M: chr-pred match-constraint
    constraint-args 2array 1array solve-next ;

GENERIC: test-constraint ( bindings chr -- ? )
