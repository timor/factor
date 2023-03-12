USING: accessors arrays chr classes combinators combinators.short-circuit kernel
lists math.parser sequences sets strings terms types.util words words.symbol ;

IN: chr.factor
FROM: syntax => _ ;

TERM-VARS:
?a ?b ?c ?d ?e ?i ?l ?k ?o ?p ?q ?r ?s ?t ?u ?n ?m ?v ?w ?x ?xs ?y
?tau1 ?tau2 ?tau3
?ys ?z ?zs ?c1 ?c2 ?s0 ?beg ?parm ?rho ?sig ?tau ?vars ;

PREDICATE: callable-word < word { [ symbol? not ] } 1&& ;

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
! Placeholder-effect?
TUPLE: RecursiveEffect < chr-pred tag effect ;
TUPLE: TypeOf < chr-pred thing type ;
TUPLE: ?TypeOf < chr-pred thing type ;
TUPLE: FixpointTypeOf < chr-pred thing type ;
TUPLE: RecursionTypeOf < chr-pred thing type ;
TUPLE: TypeOfWord < chr-pred word var ;
TUPLE: InferType < chr-pred thing ;
TUPLE: WaitFull < chr-pred type ;
TUPLE: WaitRec < chr-pred orig rec ;
TUPLE: Throws < chr-pred error ;

TUPLE: MakeSingleDispatch < chr-pred index cases target ;

! States that q3 is the composition of q1 and q2
TUPLE: ComposeType < chr-pred q1 q2 q3 ;

! Actually triggers computing composed effect and storing it into target
TUPLE: ComposeEffect < chr-pred e1 e2 target ;
! Accumulator for resulting effect predicate
TUPLE: MakeEffect < chr-pred in out locals preds target ;
! End of inference Marker
TUPLE: FinishEffect < chr-pred target ;
TUPLE: MakeUnit < chr-pred val target ;

TUPLE: Iterated < chr-pred start end ;
! TUPLE: Iterated < chr-pred val end ;

! Value-restricting preds
TUPLE: val-pred < chr-pred val ;

TUPLE: Instance < val-pred type ;
TUPLE: NotInstance < Instance ;

TUPLE: Slot < val-pred n slot-val ;
TUPLE: Element < val-pred type ;
TUPLE: Length < val-pred length-val ;
! A declaration, has parameterizing character
TUPLE: Declare < chr-pred classes stack ;

! A declaration, has no parameterizing character, just shortcut for Instance
! constraints, used to ensure stack depths and instance decls
TUPLE: Ensure < chr-pred classes stack ;

TUPLE: CallEffect < chr-pred thing in out ;
! Unused: TUPLE: MacroCallEffect < chr-pred word in out ;
TUPLE: CallRecursive < chr-pred tag in out ;
! Unused: TUPLE: NullStack < chr-pred stack ;
TUPLE: RecursivePhi < chr-pred initial stepped end ;

TUPLE: Boa < chr-pred spec in id ;
TUPLE: TupleBoa < Boa ;
TUPLE: MacroArgs < chr-pred word in out ;
TUPLE: MacroCall < chr-pred quot args in out ;

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

TUPLE: Tag < val-pred tag-var ;

! Binding for explicit referencing
TUPLE: Bind < chr-pred var src ;

! Arithmetic Reasoning
! FIXME: for some reason, this doesnt pick up correctly if it is a union def...
! UNION: expr-pred Abs Sum Eq Le Lt Ge Gt ;
TUPLE: expr-pred < val-pred ;
TUPLE: Abs < expr-pred var ;
TUPLE: Sum < expr-pred summand1 summand2 ;
TUPLE: Prod < expr-pred factor1 factor2 ;
TUPLE: Shift < expr-pred in by ;
TUPLE: BitAnd < expr-pred in mask ;
TUPLE: Eq < expr-pred var ;
TUPLE: Neq < expr-pred var ;
TUPLE: Le < expr-pred var ;
TUPLE: Lt < expr-pred var ;
! TUPLE: Ge < expr-pred val var ;
! TUPLE: Gt < expr-pred val var ;

UNION: commutative-pred Eq Neq ;

UNION: body-pred Instance NotInstance CallEffect Declare Slot CallRecursive Throws Tag
    MacroCall expr-pred Iterated ;
TUPLE: Params < chr-pred ids ;

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
! States that a parameter could be a discriminator during phi reasoning
TUPLE: Discriminator < chr-pred var ;
! States that a parameter is definitely a discriminator during phi reasoning
TUPLE: Decider < Discriminator ;
! Used during phi inference to mark constraints that are still valid...
TUPLE: Keep < chr-pred pred ;
! Marker to switch reasoning to assume disjunction of value info
TUPLE: PhiMode < chr-pred ;

! Marker to force disjunction of value info
TUPLE: FixpointMode < chr-pred ;
TUPLE: PhiDone < chr-pred ;
! Used during phi reasoning to distinguish regular ids from
! possible parametric-type-defining ones
! TUPLE: Discrims < chr-pred vars ;


GENERIC: free-effect-vars ( term -- term )
: full-type? ( type -- ? ) free-effect-vars empty? ;

M: Xor free-effect-vars
    [ type1>> ] [ type2>> ] bi [ free-effect-vars ] bi@ append ;
M: Effect free-effect-vars
    preds>> [ free-effect-vars ] gather ;
M: term-var free-effect-vars 1array ;
M: object free-effect-vars drop f ;
M: Instance free-effect-vars type>>
    dup Effect?
    [ free-effect-vars ] [ drop f ] if ;
M: CallRecursive free-effect-vars tag>> free-effect-vars ;

: fresh-effect ( effect -- effect )
    dup free-effect-vars fresh-without ;

: effect-vars ( make-effect -- set )
    [ in>> vars ] [ out>> vars union ] [ locals>> vars union ] tri ;

! All of these must be live to take collecting the pred into account
! Note that the definition of a live variable here is reachability from either input
! or output
GENERIC: live-vars ( pred -- vars )
! Will in turn define these as live
GENERIC: defines-vars ( pred -- vars )
M: chr-pred live-vars vars ;
M: object defines-vars drop f ;
M: CallEffect live-vars thing>> 1array ;
M: CallEffect defines-vars [ in>> vars ] [ out>> vars ] bi union ;
M: Slot live-vars val>> 1array ;
M: Slot defines-vars [ n>> ] [ slot-val>> ] bi 2array ;
M: Instance live-vars val>> 1array ;
M: Instance defines-vars type>> defines-vars ;
M: Tag live-vars val>> 1array ;
M: Tag defines-vars var>> 1array ;
M: Iterated defines-vars [ start>> vars ] [ end>> vars ] bi union ;
M: Sum live-vars val>> 1array ;
M: expr-pred defines-vars vars ;
! M: MacroCall live-vars out>> vars ;

