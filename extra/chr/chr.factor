USING: accessors arrays classes classes.algebra classes.tuple
combinators.private combinators.short-circuit kernel math.combinatorics
math.parser namespaces quotations sequences sets terms words ;

IN: chr

FROM: namespaces => set ;
FROM: syntax => _ ;

! * Constraint Handling Rules

ERROR: user-error error ;

TUPLE: chr heads nkept guard body match-vars existentials ;
: new-chr ( heads nkept guard body existentials class -- obj )
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

GENERIC: rule-name ( id chr -- str )
M: chr rule-name drop number>string "R" prepend ;
M: named-chr rule-name nip rule-name>> ;

! ** Constraint protocol
! Return the type to look up in index
GENERIC: constraint-type ( obj -- type )
! Return the args to match against/display
GENERIC: constraint-args ( obj -- args )


! Internal Constraints form in program
! TUPLE: chr-cons cons atoms ;
! C: <chr-cons> chr-cons

! TUPLE: builtin-cons cons atoms ;
! C: <builtin-cons> builtin-cons

! Things that can be activated
MIXIN: constraint
SINGLETON: true
SINGLETON: false
M: false constraint-type ;
M: false constraint-args drop f ;
M: true constraint-type ;
M: true constraint-args drop f ;
INSTANCE: true constraint
INSTANCE: false constraint

TUPLE: chr-pred ;
INSTANCE: chr-pred constraint

! True split, run to completion, return multiple stores
TUPLE: chr-or < chr-pred constraints ;
! The cases are run, the resulting store constraints are added to the main store
TUPLE: chr-branch < chr-pred cases ;
! Simpler version of chr-branch.  Will run body in forked context, and return all chrs with prefix
TUPLE: chr-scope < chr-pred cond body ;
! Reification of solutions
! TUPLE: And < chr-pred constraints ;
! NOTE: only having this here for printing purposes for now!
TUPLE: C < chr-pred ctx pred ;
! M: C constraint-type pred>> constraint-type ;
! M: C constraint-args ;
MIXIN: transitive

! Pre-term for splits
TUPLE: Cases < chr-pred cases ;

TUPLE: IfTe < chr-pred cond then else ;

! Context condition.  These are used to wrap up the whole store at the end...
TUPLE: Assume < chr-pred pred ;

! Match-spec telling that the current class must be preceded!
! TUPLE: bind-class { var } { args read-only } ;
! C: <bind-class> bind-class

TUPLE: chr-sub-pred class args ;
C: <chr-sub-pred> chr-sub-pred
M: chr-sub-pred constraint-type ;
M: chr-sub-pred constraint-args ;

GENERIC: match-args ( constraint -- spec )
M: object match-args constraint-args ;

! Allows matching the predicate also
TUPLE: as-pred var pred ;
C: <as-pred> as-pred
M: as-pred constraint-type pred>> constraint-type ;
M: as-pred constraint-args ;


GENERIC: lookup-index-key ( pred -- f/obj )
! indexed on the first argument
TUPLE: index1-pred < chr-pred key ;
M: object lookup-index-key drop f ;
! FIXME
! M: index1-pred lookup-index-key key>> <identity-wrapper> ;
M: index1-pred lookup-index-key key>> ;
M: chr-pred lookup-index-key class-of ;


TUPLE: any-match { cases read-only } ;
: symmetric-match ( args -- match-spec )
    all-permutations any-match boa ; inline

! Turn lexical representation into constraint object
GENERIC: pred>constraint ( obj -- chr-pred )
M: constraint pred>constraint ;

! Simplest representation
PREDICATE: pred-head-word < word chr-pred class<= ;
PREDICATE: pred-array < array ?first pred-head-word? ;
PREDICATE: fiat-pred-array < array ?first { [ word? ] [ pred-head-word? not ] [ constraint? not ] } 1&& ;

! Things that are considered non-builtin constraints
UNION: chr-constraint fiat-pred-array chr-pred chr-sub-pred as-pred ;
INSTANCE: chr-constraint constraint

! Predicates that have semantic equivalents to their logical negation
MIXIN: has-opposite
GENERIC: opposite-pred ( pred -- pred-type )

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
! UNION: chr-atom match-var ;
! GENERIC: atoms* ( obj -- )
! : atoms ( obj -- seq )
!     [ atoms* ] { } make ;
! M: object atoms* drop ;
! M: chr-atom atoms* , ;
! M: array atoms* [ atoms* ] each ;
! M: tuple atoms* tuple-slots atoms* ;
! M: constraint atoms*
!     constraint-args atoms* ;
! M: callable atoms* [ atoms* ] each ;

! Wakeup set
! GENERIC: wake-up-set ( constraint -- atoms )
! M: constraint wake-up-set atoms ;

! Called on constraints in ask position
GENERIC: test-constraint ( bindings chr -- ? )
! TODO track open replacements on suspension?
! GENERIC: constraint-fixed? ( constraint -- ? )
! M: constraint constraint-fixed? constraint-args atoms empty? ;

GENERIC: apply-substitution* ( subst constraint -- constraint )
M: false apply-substitution* nip ;
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

! * Builtin Constraints

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
M: callable apply-substitution*
    swap quote-substitution [ lift ] with-variable-on ;
: test-callable ( callable -- ? )
    ! Swap this in when suspecting that throwing errors will mess up the equivalence theory!
    ! call( -- ? ) ;
    ! [ call( -- ? ) ] [ dup user-error? [ error>> throw ] [ 2drop f ] if ] recover ;
    ! [ ( -- ? ) call-effect-unsafe ] [ dup user-error? [ error>> throw ] [ 2drop f ] if ] recover ; inline
    ( -- ? ) call-effect-unsafe ;
    ! [ dup user-error? [ error>> throw ] [ 2drop f ] if ] recover ; inline

M: callable test-constraint
    swap quote-substitution [ lift ] with-variable-on test-callable ;

: internalize-constraint ( lexical-rep -- c: constraint )
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

! ** Term hierarchy
TUPLE: type-pred < chr-pred ;

! ** Symbolic equivalences/Data-flow

TUPLE: Copies < chr-pred cond eqs ;

! NOTE: maybe should make these "flow-preds" instead?
TUPLE: Demux < chr-pred cond ins outs ;
TUPLE: Mux < chr-pred cond ins outs ;
TUPLE: Is < type-pred var src ;
TUPLE: Dup < Is ;

! ** Inference entry point
GENERIC: get-type ( quot -- type )
