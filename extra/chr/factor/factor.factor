USING: accessors arrays chr chr.state classes combinators effects kernel lexer
lists make match namespaces parser prettyprint.custom sequences strings terms
types.util ;

IN: chr.factor
FROM: syntax => _ ;

TERM-VARS:
?a ?b ?c ?d ?e ?i ?l ?k ?o ?p ?q ?r ?s ?t ?u ?n ?m ?v ?w ?x ?xs ?y
?tau1 ?tau2 ?tau3
?ys ?z ?c1 ?c2 ?s0 ?beg ?parm ?rho ?sig ?tau ?vars ;

TUPLE: state-pred < chr-pred s1 ;
TUPLE: trans-pred < state-pred s2 ;
TUPLE: val-pred < chr-pred value ;

! For cleaning up
GENERIC: state-depends-on-vars ( state-pred -- seq )
M: state-pred state-depends-on-vars drop f ;

TUPLE: Word < trans-pred word ;

TUPLE: Dispatch < trans-pred cond vset ;

TUPLE: Not < chr-pred pred ;

! TUPLE: Val < state-pred n val ;
TUPLE: Instance < val-pred s ;
TUPLE: NotInstance < chr-pred val s ;
TUPLE: ExpectInstance < chr-pred val s ;

TUPLE: Push < trans-pred lit ;

! TUPLE: AssumeEffect < trans-pred effect ;
TUPLE: AssumeWordEffect < trans-pred word effect ;
TUPLE: InferredEffect < trans-pred in out ;

TUPLE: SplitState < state-pred sa sb ;

! Phi
TUPLE: PhiState < state-pred in1 in2 ;

! Word level
TUPLE: Exec < trans-pred obj ;
TUPLE: ExecWord < trans-pred word ;
TUPLE: Generic < trans-pred word ;
TUPLE: Method < trans-pred word ;
TUPLE: SingleMethod < trans-pred word n class ;
TUPLE: DefaultMethod < trans-pred word ;
TUPLE: Definition < chr-pred word quot ;
TUPLE: Lit < val-pred literal ;

SYNTAX: Lit{ scan-object scan-object "}" expect Lit boa suffix! ;
M: Lit pprint* pprint-object ;
M: Lit pprint-delims drop \ Lit{ \ } ;
M: Lit >pprint-sequence
    [ value>> ] [ literal>> ] bi 2array ;

! TUPLE: Lit < chr-pred obj ;
TUPLE: AskLit < val-pred lit ;
TUPLE: Effect < val-pred in out ;
! TUPLE: Curried < chr-pred val parm callable ;
TUPLE: Curried < chr-pred parm q ;
TUPLE: Composed < chr-pred callable1 callable2 q ;
TUPLE: CondJump < chr-pred parent sub ;
TUPLE: CondRet < chr-pred sub parent ;

TUPLE: Assume < chr-pred type value ;

: list>stack ( list* -- list* )
    [ [ drop "v" uvar <term-var> , ] leach* ] { } make >list "rho" uvar <term-var> lappend
    ;

! list of vars
TUPLE: Stack < state-pred vals ;
M: Stack state-depends-on-vars
    [ vals>> known [ , ] leach* ] { } make ;

TUPLE: AcceptTypes < state-pred list ;
TUPLE: ProvideTypes < state-pred list ;

TUPLE: InlineQuot < trans-pred quot ;
TUPLE: InferCall < trans-pred val ;
TUPLE: InlineWord < trans-pred word ;
TUPLE: InlineCall < trans-pred word quot ;

TUPLE: Inconsistent < chr-pred constraint ;

TUPLE: Mux < state-pred bool-val cond common true false ;
! TUPLE: IfTe < state-pred cond-val true-state false-state ;
! Query marker for stack equivalence
TUPLE: Call < state-pred word in out ;
! TUPLE: Branch < trans-pred cs1 cs2 ;
TUPLE: Branch < trans-pred then else ;
M: Branch state-depends-on-vars
    [ then>> ] [ else>> ] bi 2array ;

! Compiler Entry
TUPLE: ChratInfer < chr-pred obj ;

! State connections
! TUPLE: Scope < chr-pred beg end sub-states ;
TUPLE: Scope < trans-pred stack-in stack-out sub-states ;

! Data Duplication, duplication
TUPLE: Dup < val-pred to ;
! Inverse operation
! TUPLE: Drop < state-pred val ;
! Mark value as dead.  Solvers should update their state accordingly
! TUPLE: Dead < chr-pred val ;
TUPLE: Dead < val-pred ;

TUPLE: Invalid < chr-pred val ;

! Data Flow
! Exclusive Split.
! TUPLE: Split < state-pred in out1 out2 ;
TUPLE: Split < val-pred out1 out2 ;

! dest value is derived from left value
TUPLE: Copy < val-pred dest ;

! val is derived from src1 and src2
TUPLE: Join < val-pred src1 src2 ;

! A Split implies a copy.  A Dup also implies a copy.  Things which are
! dependent on whether the target value is used twice should be derived from Dup
! and Split, not Copy.


! Def/Use
TUPLE: Def < state-pred val ;

! High-level Call Graph
TUPLE: TopEntry < chr-pred state word ;
TUPLE: Entry < state-pred word ;



TUPLE: InlineUnknown < trans-pred callable-val ;
TUPLE: Inlined < chr-pred state callable-val ;



TUPLE: InferUnknown < trans-pred val ;

! Folding
! TUPLE: LitStack < state-pred vals done? ;
TUPLE: FoldQuot < trans-pred missing quot ;
! TUPLE: AskLit < state-pred n var ;


: new-state ( -- symbol )
    "s" uvar <term-var> ;

SINGLETON: +top+
INSTANCE: +top+ match-var
SINGLETON: +end+
INSTANCE: +end+ match-var

: sub-state ( symbol -- symbol )
    dup +top+? [ drop new-state ] when
    name>> "." append uvar <term-var> ;

: seq-state ( symbol -- symbol )
    dup +top+? [ drop new-state ] when
    name>> uvar <term-var>  ;

SYMBOLS: state-in-var state-out-var ;

: state-in ( -- var )
    state-in-var get [ new-state ] unless* ; inline

: state-out ( -- var )
    state-out-var get [ new-state ] unless* ; inline

: next-state ( -- )
    state-out
    state-in uvar state-out-var set
    state-in-var set ;

! Each call advances the state
: advancing ( quot -- quot )
    [ next-state ] compose ;

: with-states ( si so quot -- )
    '[ _ state-in-var set _ state-out-var set @ ] with-scope ; inline


! : define-word-constraint ( word key effect constraints -- ) ;

! ! : parse-constraints ( effect -- seq ) ;
! : parse-constraints (  )

! TUPLE: row state vals ;
! C: <row> row

! : effect>rows ( effect -- in out )
!     [ in-var>> "si" or ]
!     [ in>>  ]

GENERIC: make-term-var ( elt -- )

M: string make-term-var
    <term-var> dup name>> ,, ;

M: pair make-term-var
    first2 [ make-term-var ]
    [ dup classoid? [ drop ] [ make-term-var ] if ] bi* ;

M: effect make-term-var
    {
        [ in-var>> [ make-term-var ] when* ]
        [ out-var>> [ make-term-var ] when* ]
        [ in>> [ make-term-var ] each ]
        [ out>> [ make-term-var ] each ]
    } cleave ;

: define-term-vars ( effect -- assoc )
    [ make-term-var ] H{ } make ;


! * Constraint Semantics for Stack-based inference

! Generally speaking, all constraints are considered to be conjunctions.
! With regards to refinement semantics, that means that there may not be a state
! where we have a set of constraints where removing one or equating two variables
! resulting in a contradiction does not denote an unreachable state.

! The most fundamental notion is that of a state.  A state denotes a momentary
! point in time between two computational steps.

! ** Basic Constraint types
!  - ~state-pred~ :: First argument is a state.  Defines a statement that is true for
!    that state
!  - ~trans-pred~ :: First 2 arguments are states.  Defines a relation between two
!    consecutive states.  This also defines reachability.  For all
!    ~{ transpred s t }~ state t is reachable iff state s is reachable.  This
!    defines a consecutive execution graph.
!  - ~Scopes~ :: Successive states are kept in ~{ Scope s1 s2 { s1.0 … s1.n }~
!    constraints, which are ~trans-pred~ that define a sequence of states that
!    makes up the transition between two states in the parent scope.  The variable
!    ~s1~ of such a scope functions as the /leader/ of the scope.  The top-level
!    scope is always ~{ Scope +top+ +end+ { … } }~.  Nested Scopes without
!    Branch constructs inbetween can be considered to be part of a parent scope.
!  - Conditions :: These are symbolic variables, which allow collecting constraints
!    into disjoint sets.  If a /condition/ is assumed, all related constraints are
!    assumed to hold as conjunction.  This allows definition of logical relations
!    between conditions.
!  - /Scope Leader/ :: The first argument of a ~Scope~ is a state, but also
!    functions as reference condition for all constraints which hold for the entire
!    scope.  The Entry point of a piece of code is the ~+top+~ symbol.
!  - ~cond-pred~ :: First variable argument is a condition.  In contrast to
!    a ~state-pred~, the statement asserted by a ~cond-pred~ must hold for the
!    entire scopse the state is part of.  If a state is given,
!    then it will be rewritten to the left-most upper-most leader, ensuring that
!    all conditional assertions in the same scope will share the same conditional
!    variable.  The ~+top+~ symbol thus makes assertions which are true for the
!    entire program.
!  - ~val-pred~ :: First argument is a variable that denotes a value.  Used to
!    describe properties of a value.  If a value is /Dead/, all assumptions about
!    it are erased.  Dead-ness is global,  If a value is dead, it is assumed to be
!    completely unused.  This happens usually under two circumstances:
!    1. The Value denoted a literal that was folded
!    2. The Value is dropped in all branches.

! * Conditional and Unconditional Statements
! A variable denoting a value is unique and global.  So the mere presence of a
! variable in a certain constraint means that the variable's part in defining the
! meaning is global.  This means that there must be distinctions between things
! that are always true, and Things that are true only conditional.

! Frequently encountered issues include:

! ** The same value enters two different Branches
!    If we assume the branch stacks of two exclusive code paths to be equal, then
!    we also assume the values to be equal.  This means that all global properties of
!    that value must be true in both branches.  E.g. for ~[ 1 ] if~, we would
!    infer that the top of stack on branch exit is literal.  This is of course not
!    necessarily true for the corresponding value in the other branch.

!    There are two general approaches to that, (TODO currently not completely
!    clear which is better: )

!    1. Create new variables for branch scopes, and denote their relation with
!       conditional ~{ Same cond v1 v2 }~  predicates.
!    2. Make all value predicates conditional
!       NOTE: *Rewriting to this approach*
!    3. Wrap all value predicates in generic ~{ Cond cond constraint }~ preds.

!    The overhead for the second variant should be smaller if there are more
!    branch-specific properties than non-branch-specific properties.  The third
!    variant is an alternative to the second, which is a general mechanism of
!    turning non-conditional statements into conditional statements.

! ** Phi-Interface for Sub-Solvers

!    As a general rule, it is desirable to have a kind of mechanism that allows
!    definition of solvers that can be asked to provide a solution for the general
!    necessary case of propagating constraints upwards to the top scope.


!    Thus, a basic protocol could be:

!    During Branch inference, all Value-related preds are wrapped in
!    ~{ Cond s { val-pred v … }~ on the state where they are created.  The branch
!    solver can then perform queries in the form of
!    ~{ ask { Phi { val-pred v c1 } { val-pred v c2 } } }~ using the modular CHRat
!    protocol, querying the sub-solver for a solution.

!    The sub-solver must ensure that parallel (partial) solver states of different
!    queries don't interfere with each other.

!    This could be achieved by letting the solvers know about the ~{ Cond c ... }~
!    format directly, or by creating existential copies, if the solver process can
!    ensure that existing knowledge will not be corrupted.

! ** Resulting Semantics
!    Note that in any case, the resulting semantics are that there are specific
!    variables in the solver state for different branches, or different predicate
!    structures which are separated by the conditions vars in the first place.
!    The difference is basically whether to expose all these values to the top
!    level, or to keep them in the sub-scopes, packing/unpacking them on demand
!    when needed.

! * Basic Inference Constraints
! ** State Preds
!    - ~{ Stack s L{ v . r } }~ :: At state s, the stack has row-definition with vars v
!      and unknown rest r. Whenever two Statements about a Stack are made which
!      turn out to be the same state, the variables are unified in the whole store.

! ** Val Preds
!    - ~{ Lit x val }~, where ~val~ is guaranteed to be a Factor ground term.
!    - ~{ Effect q in out }~, where ~in~ and ~out~ are stack lists.  Define the
!      Effect of a value ~q~ which assumed to be a callable.
!    - ~{ Type x tau }~, states that value x has type tau

! ** Trans Preds
!    - ~{ Word s t w }~ Inferred a word call between states s and t
!    - ~{ Scope s t si… }~ The states s and t are connected via the intermediate
!      states ~si~.

! ** Conditional Preds
!    - ~{ Cond c constraint }~, General container predicate, will rewrite the
!      corresponding constraint to the most-general-possible leader.
