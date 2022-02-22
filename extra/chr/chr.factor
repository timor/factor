USING: accessors arrays classes classes.algebra classes.tuple
combinators.short-circuit continuations kernel make match quotations sequences
sets terms typed words ;

IN: chr

FROM: namespaces => set ;
FROM: syntax => _ ;

! * Constraint Handling Rules


TUPLE: chr heads nkept guard body match-vars existentials ;
: new-chr ( heads nkept guard body class existentials -- obj )
    new
    swap >>existentials
    swap >>body
    swap >>guard
    swap >>nkept
    swap >>heads
    ;

! : new-prop-chr ( heads guard body class -- obj )
!     [ dup length ] 3dip new-chr ;

TUPLE: named-chr < chr rule-name ;
! : <named-chr> ( name heads nkept guard body -- obj )
!     named-chr new-chr swap >>rule-name ;

: keep/remove ( chr -- seq seq )
    [ heads>> ] [ nkept>> ] bi cut-slice ; inline

GENERIC: constraint-type ( obj -- type )
GENERIC: constraint-args ( obj -- args )

! Internal Constraints form in program
TUPLE: chr-cons cons atoms ;
C: <chr-cons> chr-cons

TUPLE: builtin-cons cons atoms ;
C: <builtin-cons> builtin-cons

TUPLE: id-cons { cons maybe{ chr-cons } } id ;
C: <id-cons> id-cons
TUPLE: active-cons { cons maybe{ id-cons } } occs j ;
C: <active-cons> active-cons

! Things that can be activated
MIXIN: constraint
SINGLETON: true
SINGLETON: false
INSTANCE: true constraint
INSTANCE: false constraint

TUPLE: chr-pred ;
INSTANCE: chr-pred constraint

! Match-spec telling that the current class must be preceded!
! TUPLE: bind-class { var } { args read-only } ;
! C: <bind-class> bind-class

TUPLE: chr-sub-pred var class args ;
C: <chr-sub-pred> chr-sub-pred
M: chr-sub-pred constraint-type ;
M: chr-sub-pred constraint-args ;


! Turn lexical representation into constraint object
GENERIC: pred>constraint ( obj -- chr-pred )
M: constraint pred>constraint ;

! Simplest representation
PREDICATE: pred-head-word < word chr-pred class<= ;
PREDICATE: pred-array < array ?first pred-head-word? ;
PREDICATE: fiat-pred-array < array ?first { [ word? ] [ pred-head-word? not ] } 1&& ;

! Things that are considered non-builtin constraints
UNION: chr-constraint fiat-pred-array chr-pred chr-sub-pred ;
INSTANCE: chr-constraint constraint

: check-slots>tuple ( seq class -- tuple )
    2dup all-slots [ length ] same? [ "wrong # tuple args" 3array throw ] unless
    slots>tuple ;

M: pred-array pred>constraint
    unclip-slice check-slots>tuple ;

M: sequence pred>constraint [ pred>constraint ] map ;

M: chr-pred constraint-type class-of ;
M: chr-pred constraint-args tuple-slots ;
M: fiat-pred-array constraint-type first ;
M: fiat-pred-array constraint-args rest-slice ;

! * Existential callout
TUPLE: generator vars body ;
C: <generator> generator
INSTANCE: generator constraint
M: generator pred>constraint
    clone [ [ pred>constraint ] map ] change-body ;


TUPLE: is-val var body ;
C: <is-val> is-val
INSTANCE: is-val constraint
M: is-val pred>constraint
    clone [ [ pred>constraint ] map ] change-body ;

! TODO: properly fix the variable set in the suspension instead of this mess...
UNION: chr-atom match-var ;
GENERIC: atoms* ( obj -- )
: atoms ( obj -- seq )
    [ atoms* ] { } make ;
M: object atoms* drop ;
M: chr-atom atoms* , ;
M: array atoms* [ atoms* ] each ;
M: tuple atoms* tuple-slots atoms* ;
M: constraint atoms*
    constraint-args atoms* ;
M: callable atoms* [ atoms* ] each ;

! Wakeup set
GENERIC: wake-up-set ( constraint -- atoms )
M: constraint wake-up-set atoms ;

! Called on constraints in ask position
GENERIC: test-constraint ( bindings chr -- ? )
! TODO track open replacements on suspension?
GENERIC: constraint-fixed? ( constraint -- ? )
M: constraint constraint-fixed? constraint-args atoms empty? ;

GENERIC: apply-substitution* ( subst constraint -- constraint )
M: true apply-substitution* nip ;
M: chr-pred apply-substitution*
    [ tuple-slots swap lift ]
    [ class-of ] bi slots>tuple ;
M: fiat-pred-array apply-substitution*
    unclip-slice [ swap lift ] dip prefix ;

M: generator apply-substitution*
    clone [ [ apply-substitution* ] with map ] change-body ;

M: is-val apply-substitution*
    clone [ [ apply-substitution* ] with map ] change-body ;

! This one is generated, and reflects the modifications to the internal equality
! state.  It can be matched on, but it is kind of a "passive" builtin, generated
! by the "==!" command
! TODO: perhaps also insert the reflexive constraint? Normaly shouldn't be
! needed, since regular tests should be conducted using ==, but it allows
! "exporting" the equality solver state
! PREDICATE: eq-constraint < fiat-pred-array first \ = eq? ;
TUPLE: eq-constraint lhs rhs subsumed-vars ;
: <eq-constraint> ( lhs rhs -- obj ) f eq-constraint boa ;

! * Arbitrary guards
INSTANCE: callable constraint
M: callable apply-substitution* swap lift ;
: test-callable ( callable -- ? )
    ! call( -- ? ) ;
    [ call( -- ? ) ] [ 2drop f ] recover ;

M: callable test-constraint
    swap lift test-callable ;

TYPED: internalize-constraint ( lexical-rep -- c: constraint )
    pred>constraint ; inline

: internalize-constraints ( seq -- seq )
    dup t = [ [ internalize-constraint ] map ] unless ;

! Returns all vars in the heads and guard
: rule-match-vars ( chr-rule -- seq )
    [ heads>> vars ]
    [ guard>> vars ] bi union ;

: internalize-rule ( chr-rule -- chr-rule )
    clone
    [ internalize-constraints ] change-heads
    [ internalize-constraints ] change-guard
    [ internalize-constraints ] change-body
    dup rule-match-vars >>match-vars
    ;
