USING: accessors arrays chr classes classes.predicate classes.tuple
classes.union combinators combinators.short-circuit kernel lists math.parser
sequences sets strings terms types.util words words.symbol ;

IN: chr.factor
FROM: syntax => _ ;

TERM-VARS:
?a ?b ?c ?d ?e ?i ?l ?k ?o ?p ?q ?r ?s ?t ?u ?n ?m ?v ?w ?ws ?x ?xs ?y
?tau1 ?tau2 ?tau3
?ys ?z ?zs ?c1 ?c2 ?s0 ?beg ?parm ?rho ?sig ?tau ?vars ;

PREDICATE: callable-word < word { [ symbol? not ] } 1&& ;


! * Semantic Notes

! ** Type declarations and dispatch
! There is a chicken-and-egg situation to solve.  With regards to semantic
! subtyping, a value having a certain type means that this value fulfills certain
! properties.  If these properties are to be reasoned about, they must become
! apparent during inference at the correct positions.  There are several cases to
! consider

! *** Explicit predicate words
!     This is the most obvious case: If a ~foo?~ word of class ~foo~ is
!     encountered, the expanded instance check's predicates are inferred for
!     composition, ususally resulting in an Xor type.

! *** Typed Definitions
!     These are explicitly defined to have coercing behaviour with regards to the
!     input classes.  However, the implementation suggests that this is actually
!     delegated to ~declare~?

! *** Default input/output types
!     Primitive words have these defined per fiat power.  They are basically used
!     to "bootstrap" type checking by having default instance assumptions to work with.

! *** GenericDispatch
!     This is like typed definitions, but the dispatch process is stateful.  Thus,
!     the strategy is to actually follow the predicate decision path.

! ** The Role of Declarations
!    On one hand, declarations are nominative, i.e. we simply state that a value
!    belongs to a certain type.  On the other hand, declarations are used like
!    refinements.

! ** Nominative vs. predicative/semantic types
!    Declarations are kept as nominative declarations.  Instance predicates are
!    used on the semantic level.   This means we can keep reasoning on a nominative
!    level, while expanding e.g predicates to have the desired effect.

! ** Relations and Xor Types
! There seems to be a need to distinguish between not creating union types based on
! control flow or continuation-level data flow, and not creating union types
! based on predicates/relations.
! Example came from bounds-check?, relating length l of a sequence to access at
! location n.  Inference returns 3 types, two of which
! return t, while one returns f.  There are different reasons associated to
! these cases:
! 1. Returns o = t not f, because 0 <= n  and n <= l
! 2. Returns o = f not t, because n < 0
! 3. Returns o = f not t, because n >= l
! The knowledge we actually want to keep is two logical
! expressions:
! 1. o <=> ( n >= 0 )
! 2. o <=> ( n <= l ) i.e.
! Which means o <=> (n >= 0)&(n <= l)

! The Problem with the current approach is that there is only exactly one order
! of phi-unification which would yield this result, which is A = 1. + 2., then B
! = 1. + 3., then finally C = A + B.

! One thing to consider that it is probably impossible to store the needed
! knowledge with only the 3 Xor cases, because we have 2x2=4 cases to consider.
! It is possible though to store this information in two equivalence predicates.
! => Well, akshually, that's not the case.  3 Xor cases are enough.

! ** Liveness of "internal" variables

! Up until now, predicates' holes were considered in/out polarity.  This
! however, brings problems with liveness analysis for variables.  It's probably
! necessary to have kind of a def/use-equivalent approach.  This should be
! possible by not arbitrarily throwing around the order of predicates in
! seemingly symmetric or commutative relation predicates.  This might make it
! necessary to introduce a number of new rules, but ideally these should
! coincide with the ones needed to only keep the relevant predicates alive in
! the first place...
! Alternatively, a more general approach could be tried with explicitly
! declaring which var slots are inputs and outputs, respectively.

! * Helpers for generating declared effects

GENERIC: elt>var ( i elt -- obj )
M: f elt>var drop number>string "v" prepend utermvar ;
M: string elt>var nip utermvar ;
M: pair elt>var
    first2 drop elt>var ;

: elt-vars ( seq -- seq )
    [ swap elt>var ] map-index ;
: effect>stack-elts ( effect -- lin lout )
    [ in>> elt-vars <reversed> >list ]
    [ out>> elt-vars <reversed> >list ] bi ;

:: add-row-vars ( lin lout effect -- lin lout )
    effect [ in-var>> ] [ out-var>> ] bi
    [ dup [ utermvar ] when ] bi@
    :> ( i o )
    { { [ i o [ not ] both? ]
        [ "rho" utermvar :> rho
          lin rho list*
          lout rho list* ] }
      { [ i o [  ] both? ]
        [ lin i list*
          lout o list* ] }
      [ lin __ list* lout __ list* ]
    } cond ;

: effect>stacks ( effect -- lin lout )
    [ effect>stack-elts ]
    [ add-row-vars ] bi ;

! * Compositional approach

! ** Effect Type
! An effect type would represent a typed Factor Effect
! ~( ..a x: integer y: number -- y x ..a )~  as
! #+begin_example factor
! P{ Effect L{ ?y ?x . ?a } L{ ?x ?y ?z . ?a } {
!   P{ Instance ?x integer }
!   P{ Instance ?y number }
!   }
! }
! #+end_example
! This is equivalent with the following logical expression:
! For all x, y, a, b: If the input matches the given form:
! - The output matches the given form
! - The value x is an instance of integer
! - The value y is an instance of number
! - We know nothing about the value ?z

! Problem: ~z~ could be interpreted as an existential variable, but also as a universally
! quantified one.  This is most interesting for union types, e.g. for the
! ~[ swap ] when~ example, where the union type of ~( x y -- y x )~ and
! ~( ..b -- ..b )~ has to be calculated.

! Now this is a bit problematic, concerning the semantics.
! The intersection check can be performed if we assume the same inputs, so firs we
! unify ~L{ ?y ?x . ?a } ==! ?b~.  This creates the following Effect Types:
! #+begin_example factor
! P{ Effect L{ ?y ?x . ?a } L{ ?x ?y . ?a } }
! P{ Effect L{ ?y ?x . ?a } L{ ?y ?x . ?a } }
! #+end_example

! Note that for making an intersection type, unification of this would actually be
! possible, and return the side condition that ~?x = ?y~.  However, the output
! stack itself can actually be considered a dependent type of the input stack.  In
! order for these to have the chance to intersect, they must be α-equivalent under
! the input stack bindings. (There can be existentials in the outputs)

TUPLE: Effect < chr-pred in out parms preds ;
TUPLE: TypeOf < index1-pred type ;
TUPLE: ?TypeOf < chr-pred thing type ;
! Can be used during inference, will either trigger nested inference or
! immediately answer
TUPLE: ?DeferTypeOf < ?TypeOf ;
TUPLE: FixpointTypeOf < chr-pred thing type ;
TUPLE: RecursionTypeOf < chr-pred thing type ;
TUPLE: RecursiveCallTypeOf < chr-pred thing type ;
TUPLE: TypeOfWord < chr-pred word var ;
TUPLE: InferType < chr-pred thing ;
TUPLE: WaitFull < chr-pred type ;
TUPLE: WaitRec < chr-pred orig rec ;
TUPLE: Throws < chr-pred error ;

TUPLE: MakeSingleDispatch < chr-pred index cases exclude target ;

TUPLE: GenericDispatch < chr-pred word on out-vals in out ;
TUPLE: MakeGenericDispatch < chr-pred word effect target ;

! States that q3 is the composition of q1 and q2
TUPLE: ComposeType < chr-pred q1 q2 q3 ;
! Reinfer effect body
TUPLE: ReinferEffect < chr-pred type target ;

! Actually triggers computing composed effect and storing it into target
TUPLE: ComposeEffect < chr-pred e1 e2 target ;
TUPLE: Spool < chr-pred target preds ;
! Mode wrapper
TUPLE: CP < chr-pred tag pred ;
! Accumulator for resulting effect predicate
TUPLE: MakeEffect < chr-pred in out locals preds target ;
TUPLE: MakePhiEffect < MakeEffect ;
! Suspended MakeEffect until type is known
TUPLE: SuspendMakeEffect < MakeEffect depends-on ;
! End of inference Marker
TUPLE: FinishEffect < chr-pred target ;
TUPLE: MakeUnit < chr-pred val target ;

TUPLE: WrapClasses < chr-pred in out effect target ;
TUPLE: WrapDefaultClasses < chr-pred word effect target ;

! Holds references to the stack at loop entry,
! loop iteration, and loop exit
! TUPLE: Iterated < chr-pred entry loop-entry loop-exit exit ;
TUPLE: Iterated < chr-pred tag stuff ;
TUPLE: LoopVar < chr-pred stuff ;

! Value-restricting preds
TUPLE: val-pred < chr-pred val ;

! Semantic
TUPLE: Instance < val-pred type ;
! Nominative
TUPLE: DeclaredInstance < Instance ;
TUPLE: DeclaredNotInstance < Instance ;

! Need for math method expansion?
TUPLE: Coerce < val-pred class ;

TUPLE: expr-pred < val-pred ;
! TODO: not sure why this is a val-pred on the object!
TUPLE: Slot < val-pred n slot-val ;
! Element class?
TUPLE: Element < val-pred type ;
TUPLE: Length < val-pred length-val ;
TUPLE: Nth < val-pred seq n ;
! A declaration, has parameterizing character
TUPLE: Declare < chr-pred classes stack ;

! A declaration, has no parameterizing character, just shortcut for Instance
! constraints, used to ensure stack depths and instance decls
TUPLE: Ensure < chr-pred classes stack ;

TUPLE: CallEffect < chr-pred thing in out ;
TUPLE: ApplyEffect < chr-pred effect in out ;
! Has CallEffect and Instance properties
TUPLE: CallXorEffect < chr-pred type in out ;
! Unused: TUPLE: MacroCallEffect < chr-pred word in out ;
TUPLE: CallRecursive < chr-pred tag in out ;
! The same as above, but different
TUPLE: CallUnknown < CallEffect ;
TUPLE: CallSite < chr-pred word var ;

TUPLE: CallsRecursive < chr-pred word other-words ;
TUPLE: PartialRecursive < chr-pred word temp-word ;

TUPLE: Boa < chr-pred spec in id ;
TUPLE: TupleBoa < Boa ;
! explicitly referencing out-quot here for live-ness
TUPLE: MacroExpand < chr-pred quot args in out-quot ;
! Used for anonymous expansion
TUPLE: ExpandQuot < MacroExpand num-args ;
TUPLE: InstanceCheck < chr-pred class-arg quot complement ;

! Macro expansion, folding
TUPLE: FoldStack < chr-pred stack n ;
TUPLE: FoldCall < chr-pred stack n quot target ;

! TUPLE: Recursive < chr-pred tag effect ;
TUPLE: Recursive < chr-pred tag ;
TUPLE: Continue < chr-pred tag ;
TUPLE: Recursion < chr-pred tag back-to from ;
TUPLE: MakeXor < chr-pred type1 type2 target ;

TUPLE: CheckXor < chr-pred quot branch target ;
TUPLE: MakeRecursion < chr-pred type target ;
TUPLE: MakeFoldable < chr-pred type target ;
TUPLE: Copy < chr-pred type target ;
TUPLE: CheckFixpoint < chr-pred quot type ;

TUPLE: Xor < chr-pred type1 type2 ;
TUPLE: And < chr-pred types ;
! TUPLE: Intersection < chr-pred type types ;
TUPLE: Intersection < chr-pred type types ;
TUPLE: Union < chr-pred type types ;
TUPLE: SubType < chr-pred sub super ;

! TUPLE: Use < chr-pred val ;
TUPLE: Let < chr-pred var val type ;

TUPLE: Invalid < chr-pred ;
! TUPLE: Invalid < chr-pred var ;

TUPLE: Tag < val-pred tag-var ;

! Binding for explicit referencing
TUPLE: Bind < chr-pred var src ;

! Arithmetic Reasoning
! FIXME: for some reason, this doesnt pick up correctly if it is a union def...
! UNION: expr-pred Abs Sum Eq Le Lt Ge Gt ;
TUPLE: MathCall < chr-pred word in out ;
TUPLE: Abs < expr-pred var ;
TUPLE: Sum < expr-pred summand1 summand2 ;
TUPLE: Prod < expr-pred factor1 factor2 ;
! { Mod  }
! TUPLE: Mod < expr-pred
TUPLE: Shift < expr-pred in by ;
TUPLE: BitAnd < expr-pred in mask ;
TUPLE: BitNot < expr-pred in ;
TUPLE: rel-pred < expr-pred val2 ;
! This represents number equality
TUPLE: Num= < rel-pred ;
! This represents equal? equality
TUPLE: Eq < rel-pred ;
! TUPLE: StrictEq < Eq ;
TUPLE: Neq < rel-pred ;
TUPLE: NotSame < Neq ;
TUPLE: Le < rel-pred ;
! TUPLE: Lt < rel-pred ;
TUPLE: Lt < Le ;
! TUPLE: Ge < expr-pred val var ;
! TUPLE: Gt < expr-pred val var ;
! TUPLE: Counter < val-pred from to by ;
TUPLE: Counter < chr-pred start iter-in iter-out end delta ;

TUPLE: <==> < chr-pred flag consequent ;

GENERIC: opposite-predicate ( pred -- pred/f )
M: Eq opposite-predicate tuple-slots Neq slots>tuple ;
M: Neq opposite-predicate tuple-slots Eq slots>tuple ;
M: Lt opposite-predicate tuple-slots <reversed> Le slots>tuple ;
M: Le opposite-predicate tuple-slots <reversed> Lt slots>tuple ;
! HA! Trap? Not correct if we argue semantically.  Handled by Xor expansion
! of instance? ?
! M: Instance opposite-predicate
! This should be fine because it's nominative? In any case, don't try rightaway...
M: DeclaredInstance opposite-predicate
    tuple-slots DeclaredNotInstance slots>tuple ;

! commutative binary operations
UNION: binop Sum Prod ;

UNION: lt-pred Le Lt ;
UNION: symmetric-pred Eq Neq Num= ;
! No, that was incorrect.  Simply matching against all permutations does not fix
! the bindings.  For that, we need a two-step process
! M: symmetric-pred match-args
!     call-next-method symmetric-match ;

! Catch some Primitive Calls for easier conversion
TUPLE: PrimCall < chr-pred word in out ;

! Reference counting on dup'd vars. Counts the copies.
! Basically distributed def-use. Vars are dead if the value is -1?
! TUPLE: ref-pred < chr-pred  ;
! TUPLE: Ref+ < ref-pred vars ;
! TUPLE: Ref- < ref-pred vars ;
! TUPLE: Refs < ref-pred map ;
UNION: body-pred val-pred CallEffect CallXorEffect Declare CallRecursive Throws
    MacroExpand
    Iterated
    LoopVar GenericDispatch <==> MathCall PrimCall Counter
    ! ! Taking this into account because of generics reinference right now.
    ! ApplyEffect
    ;

TUPLE: CheckPhiStack a b res ;

UNION: valid-effect-type Effect Xor ;
UNION: valid-type Effect classoid ;

! Phi stuff

TUPLE: PhiSchedule < chr-pred quot list target ;
TUPLE: DisjointRoot < chr-pred effect ;
TUPLE: DestrucXor < chr-pred branch ;
TUPLE: RebuildXor < chr-pred effect target ;
TUPLE: CurrentPhi < chr-pred effect ;
TUPLE: MakeUnion < chr-pred effect1 effect2 target ;
! States that a parameter discriminates two sets during phi reasoning
TUPLE: Discriminator < chr-pred var ;
! States that a parameter is definitely a decider for two sets during phi reasoning
TUPLE: Decider < Discriminator ;
! Used during phi inference to mark constraints that are still valid...
TUPLE: Keep < chr-pred pred ;
! Marker to switch reasoning to assume disjunction of value info
TUPLE: PhiMode < chr-pred ;
! Marker to switch reasoning to assume conjunction of value info
TUPLE: CompMode < chr-pred ;

! This is used during phi-mode reasoning to hold the list of parameters that have not
! been unified.
TUPLE: Params < chr-pred vars ;

! This is an implication relation for parameter membership
! Useful for functions that can be folded/reduced
TUPLE: ImpliesParam < chr-pred present include ;

! Helpers, cleaned up like unused body preds at the end
! MIXIN: inference-pred
! INSTANCE: ImpliesParam inference-pred
! INSTANCE: Ensure inference-pred

! Marker to force disjunction of value info
TUPLE: FixpointMode < chr-pred ;
TUPLE: PhiDone < chr-pred ;
! Used during phi reasoning to distinguish regular ids from
! possible parametric-type-defining ones
! TUPLE: Discrims < chr-pred vars ;

! Liveness
TUPLE: liveness-pred < chr-pred ;
TUPLE: Live < liveness-pred vars ;
TUPLE: Roots < Live ;
! TUPLE: Locals < Live ;
! TUPLE: In < Live ;
! TUPLE: Out < Live ;
! In/out semantics
TUPLE: Dep < liveness-pred from to ;
TUPLE: Rel < liveness-pred from to via ;


GENERIC: free-effect-vars ( term -- seq )
: full-type? ( type -- ? ) free-effect-vars empty? ;

M: Xor free-effect-vars
    [ type1>> ] [ type2>> ] bi [ free-effect-vars ] bi@ append ;
M: Effect free-effect-vars
    preds>> [ free-effect-vars ] gather ;
M: term-var free-effect-vars 1array ;
M: object free-effect-vars drop f ;
M: Instance free-effect-vars type>>
    dup term-var? not
    [ free-effect-vars ] [ drop f ] if ;
M: CallRecursive free-effect-vars tag>> free-effect-vars ;
M: CallXorEffect free-effect-vars type>> free-effect-vars ;
M: CallUnknown free-effect-vars thing>> free-effect-vars ;
! M: CallXorEffect free-effect-vars
!     [ then>> ] [ else>> ] bi
!     [ free-effect-vars ] bi@ union ;
! We expect an expanded macro to have properly substituted type vars
! M: ApplyEffect free-effect-vars effect>> free-effect-vars ;

GENERIC: bound-effect-vars ( term -- seq )
M: object bound-effect-vars drop f ;
M: Effect bound-effect-vars
    {
        [ in>> vars ] [ out>> vars union ]
        [ parms>> vars union ]
        [ preds>> [ bound-effect-vars ] gather union ]
    } cleave ;
M: Xor bound-effect-vars
    [ type1>> bound-effect-vars ]
    [ type2>> bound-effect-vars ] bi union ;
M: Instance bound-effect-vars type>> bound-effect-vars ;
M: CallXorEffect bound-effect-vars type>> bound-effect-vars ;
! M: CallXorEffect bound-effect-vars
!     [ then>> ] [ else>> ] bi
!     [ bound-effect-vars ] bi@ union ;

: fresh-effect ( effect -- effect )
    ! dup free-effect-vars fresh-without ;
    dup bound-effect-vars fresh-with ;

: make-effect-vars ( make-effect -- set )
    [ in>> vars ] [ out>> vars append ] [ locals>> vars union ] tri ;

! All of these must be live to take collecting the pred into account
! Note that the definition of a live variable here is reachability from either input
! or output
GENERIC: live-vars ( pred -- vars )
! Will in turn define these as live
GENERIC: defines-vars ( pred -- vars )
! This is special for predicates where parts of the variables intersect in
! order to consider it live.
! TODO: Ideally, this should only be needed for expansions where not all outputs
! are known to be used anymore...
GENERIC: intersects-live-vars ( pred -- vars )
! HACK Do this for sums and products for now to fix tests
M: binop intersects-live-vars vars ;
M: object intersects-live-vars drop f ;
M: chr-pred live-vars vars ;
M: object defines-vars drop f ;
! ! TODO Maybe don't need this if type-inference checks are done using ExpandMacro?
! M: CallEffect intersects-live-vars in>> vars ;
M: CallEffect live-vars thing>> 1array ;
! XXX pure guessing...
! M: CallUnknown live-vars out>> vars ;
! ! M: CallEffect defines-vars [ in>> vars ] [ out>> vars ] bi union ;
! M: CallEffect defines-vars [ out>> vars ] [ thing>> 1array ] bi union ;
! M: CallEffect defines-vars vars ;
! TODO: add inputs to defined vars of CallEffect, as they are definitely known to exist...
! M: CallEffect defines-vars out>> vars ;
! TODO: remove this and use deps like callxoreffect?
! M: CallEffect defines-vars [ in>> vars ] [ out>> vars append ] bi ;
M: CallXorEffect intersects-live-vars in>> vars ;
! NOTE: keeping references to input vars here, since they are lazy intermediates...
M: CallXorEffect live-vars
    [ in>> vars ]
    [ out>> vars append ] bi ;
M: CallXorEffect defines-vars
    type>> defines-vars ;
    ! [ then>> ] [ else>> ] bi
    ! [ [ live-vars ] gather ] bi@ union ;
! M: CallXorEffect defines-vars
!     [ then>> ] [ else>> ] bi
!     [ [ defines-vars ] gather ] bi@ union ;
! NOTE: also keeping references to input vars here, to prevent (partially) known input vals from being collected
M: MacroExpand defines-vars
    [ out-quot>> vars ]
    [ in>> vars append ] bi
    ;
M: MacroExpand intersects-live-vars in>> vars ;
! M: MacroExpand live-vars in>> vars ;
! For now, have prim calls be "contagious", to make sure we don't miss any!
M: PrimCall intersects-live-vars vars ;
M: PrimCall defines-vars vars ;

! M: val-pred live-vars val>> 1array ;
! M: val-pred defines-vars tuple-slots rest-slice vars ;
! M: Slot live-vars val>> 1array ;
! M: Slot defines-vars [ n>> vars ] [ slot-val>> vars append ] bi ;
! M: Length live-vars val>> 1array ;
! M: Length defines-vars length-val>> 1array ;
M: Instance live-vars val>> 1array ;
! M: Instance defines-vars type>> defines-vars ;
! M: Tag live-vars val>> 1array ;
! M: Tag defines-vars var>> 1array ;
M: Iterated intersects-live-vars
    stuff>> vars ;
M: Iterated defines-vars
    stuff>> vars ;
    ! [ start>> vars ] [ end>> vars ] bi union ;
! TODO: there might be a pattern here...
! M: Sum live-vars val>> 1array ;
! M: Counter live-vars val>> 1array ;
! M: expr-pred defines-vars vars ;
! M: MacroCall live-vars out>> vars ;
M: GenericDispatch intersects-live-vars
    out-vals>> vars ;
    ! [ in>> ] [ out>> ] bi [ vars ] bi@ union vars ;
! TODO: unsure about the following
! Pretty sure that it's not ok, because this is not a macro!
! M: GenericDispatch defines-vars
!     [ in>> vars ]
!     [ out-vals>> vars append ] bi ;


! NOTE: don't use internal optimized implementations here
GENERIC: make-pred-quot ( class -- quot )

! { real fixnum array }
! [ dup real? [ nip ] [ dup fixnum? [ nip ] [ array? ] if* ] if* ]
M: union-class make-pred-quot
    "members" word-prop <reversed> unclip "predicate" word-prop
    swap
    [ ! ( acc class )
        "predicate" word-prop swap
        '[ dup @ [ nip ] _ if* ]
    ] each ;

! NOTE: relies on implementation detail of the predicate quotation being a singular
! quotation!
M: predicate-class make-pred-quot "predicate" word-prop first def>> ;
