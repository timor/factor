USING: accessors arrays chr chr.factor chr.factor.defs chr.parser chr.state
classes classes.algebra combinators combinators.short-circuit effects generic
generic.math kernel kernel.private lists math math.parser quotations sequences
sets strings terms types.util words words.symbol ;

IN: chr.factor.stack


! * Util for effect/stack conversions

GENERIC: elt>var ( i elt -- obj )
M: f elt>var drop number>string "v" prepend utermvar ;
M: string elt>var nip utermvar ;
M: pair elt>var
    first2 drop elt>var ;

: elt-vars ( seq -- seq )
    [ swap elt>var ] map-index ;

! * Eval State model

PREDICATE: callable-word < word { [ symbol? not ] } 1&& ;

! Elements represent type expressions, which have "Have" semantics
TUPLE: Stack < chr-pred content ;
TUPLE: Eval < chr-pred code ;
TUPLE: Eval1 < chr-pred thing ;
TUPLE: Exec < chr-pred word in out ;
TUPLE: ApplyEffect < chr-pred in out effect ;
TUPLE: InferEffect < chr-pred thing in out def ;
TUPLE: Inferred < chr-pred thing start ;

! Types

! Definition
TUPLE: Type < chr-pred var type ;

! Effect Type
TUPLE: Effect < chr-pred in out preds ;

! Type of "expressions"
TUPLE: TypeOf < chr-pred thing type ;

! Refined Type
TUPLE: Refine < chr-pred type preds ;

! Typecase
TUPLE: TypeCase < chr-pred var cond then else ;

! Predicate defs
TUPLE: Pred < chr-pred var expr ;
! Simplest predicate
TUPLE: Instance < chr-pred var type ;

! Expresses that the types on the stack must be subtypes of the list of types in types, which is done
! typically at word calls, e.g. for +
! i.e. { ExpectType L{ ?x1 ?x2 . ?rho } { number number } }
TUPLE: ExpectType < chr-pred stack types ;

TUPLE: IfTe < chr-pred bool then else ;
TUPLE: Param < chr-pred var parm type ;
TUPLE: Xor < chr-pred var type1 type2 ;
! TUPLE: DisjointMember < chr-pred type union ;

! Arithmetic Sub-Solver
TUPLE: Sum < chr-pred result x y ;

CHRAT: chr-stack { }

! ** Type stack operations


! *** Destructuring
CHR: did-expect-types @ // { ExpectType __ +nil+ } -- | ;
CHR: expecting-types @ // { ExpectType L{ ?x . ?xs } L{ ?y . ?ys } } -- |
{ ExpectType ?x ?y }
{ ExpectType ?xs ?ys } ;

! NOTE: destructive
CHR: expand-expect-types-right @ // { ExpectType L{ ?x . ?xs } ?b } -- [ ?b term-var? ] |
[ ?b L{ ?y . ?ys } ==! ]
{ ExpectType ?x ?y }
{ ExpectType ?xs ?ys } ;

CHR: expand-expect-types-left @ // { ExpectType ?a L{ ?y . ?ys } } -- [ ?a term-var? ] |
[ ?a L{ ?x . ?xs } ==! ]
{ ExpectType ?x ?y }
{ ExpectType ?xs ?ys } ;

! *** Asserting required types
CHR: check-expect-type @ // { ExpectType A{ ?x } A{ ?rho } } --
! Wrapping this to presever wrapper during expansion
[ { ?x } first dup wrapper? [ <wrapper> :>> ?tau ] [ :>> ?tau ] if ] |
[ ?tau ?rho class<= [ { ?tau ?rho "expect type failed" } throw ] unless f ] ;

! Subtype semantics for effects: If we expect an (inferred, given) effect rho -> sig
! to fulfill the expectations of (call-site) effect a -> b, then:
! - Caller-provided input types must be subset of callee-expected types ( a < rho )
! - Callee-provided output types must be subset of caller-expected types ( sig < b )

CHR: expect-effects @ // { ExpectType P{ Effect ?rho ?sig A{ f } } P{ Effect ?a ?b A{ f } } } -- |
{ ExpectType ?a ?rho }
{ ExpectType ?sig ?b } ;

! Additional complication with refinement types: for { ExpectType given: { Effect rho sig p.. } required: { Effect a b q.. } }
! In addition to the above, the combination of constraints from both specifications must be met

CHR: expect-effects-pred-both @ // { ExpectType P{ Effect ?rho ?sig ?k } P{ Effect ?a ?b ?l } } -- |
{ ExpectType ?a ?rho }
{ ExpectType ?sig ?b }
[ ?k ]
[ ?l ]
    ;

! *** Instantiate "type scheme" when we expect a literal to fulfill an effect
! Semantics: We expect the singleton type of a callable to fulfill some (call-site)
! effect spec
CHR: already-inferred-effect @ { TypeOf ?q ?tau } // { ExpectType A{ ?q } P{ Effect ?a ?b ?k } } -- [ ?tau Effect? ] |
[| | ?tau [ in>> ] [ out>> ] [ preds>> ] tri :> ( in out preds )
 ?tau in vars out vars union fresh-with :> inst
 { ExpectType inst P{ Effect ?a ?b ?k } }
 ! ! One additional layer of wrapping to guard against equal vars...
 ! { ExpectType inst P{ Effect ?rho ?sig ?k } }
 ! { ExpectType ?a ?rho }
 ! { ExpectType ?sig ?b }
 ! 3array
] ;

! *** Trigger inference of unknown quot
! FIXME: This could just be a symptom cure for not creating intersection arrows early enough!
! XXX: Nope, didnt help...
CHR: infer-only-once @ { InferEffect ?c __ __ ?q } { TypeOf ?q ?c } // { InferEffect ?d __ __ ?q } { TypeOf ?q ?d } -- | ;

CHR: infer-effect @ { ExpectType A{ ?q } P{ Effect ?a ?b ?k } } // -- [ ?q callable? ] |
{ InferEffect ?c ?rho ?sig ?q }
{ TypeOf ?q ?c }
    ;

! *** Single Type variable

! Semantics: { Expect tau sig } Is valid, iff all actual values of tau are possible values of sig, i.e. val(tau) ⊆ val(sig)
! If sig is given, then that establishes an upper bound for tau, so if tau represents all possible values, the set bounded by sig is exactly sig.
CHR: establish-expect-type-rhs @ // P{ ExpectType ?x A{ ?rho } } -- [ { ?rho } first classoid? ] |
[ ?x { ?rho } first ==! ] ;
! { TypeOf ?x ?rho } ;

! Semantics: { Expect tau sig } with tau being given a concrete value, and sig
! an unknown value.  val(tau) ⊆ val(sig) does always hold.  However, we also
! know that, in a top-level context, there is actually no way that sig will be
! any larger than tau, so we can establish a lower bound for sig, which is indeed exactly tau...

! However, if we already have a type, for it, then replace that
CHR: known-expected-type-lhs @ { TypeOf ?q ?tau } // { ExpectType A{ ?q } ?sig } -- [ ?sig term-var? ] |
[ ?sig ?tau ==! ] ;
! { ExpectType ?tau ?sig } ;

CHR: establish-expect-type-lhs-effect @ // { ExpectType ?tau ?sig } -- [ ?tau Effect? ] [ ?sig term-var? ] |
[ ?sig ?tau ==! ] ;

CHR: establish-expect-type-lhs @ // { ExpectType A{ ?tau } ?sig } -- [ { ?tau } first classoid? ] [ ?sig term-var? ] |
[ ?sig { ?tau } first ==! ] ;

! *** Symbolic transitivity
! NOTE: destructive
CHR: expect-unknown-type-is-same @ // P{ ExpectType ?a ?b } -- [ ?a term-var? ] [ ?b term-var? ] |
[ ?a ?b ==! ] ;
! CHR: expect-var-is-transitive @ // { ExpectType ?a ?b } { ExpectType ?b ?c } -- [ ?b term-var? ] |
! { ExpectType ?a ?c } ;


! ** Subordinate inference
CHR: do-sub-infer-effect @ // { InferEffect ?c ?rho ?sig ?q } { Eval ?p } { Effect ?a A{ f } ?k } { Stack ?b } -- |
{ Effect ?rho f f }
{ Stack ?rho }
{ Eval ?q }
{ Inferred ?c ?rho }
{ Effect ?a f ?k }
{ Stack ?b }
{ Eval ?p } ;

CHR: collect-sub--effect @ // { Inferred ?c ?rho } { Effect ?rho ?sig ?k } -- |
[ ?c P{ Effect ?rho ?sig ?k } ==! ] ;


! ** Stack-state advancing

! Internal representation of sequence of words is list...
CHR: eval-quot @ // { Eval ?p } -- [ ?p callable? ] [ ?p >list :>> ?q ] |
{ Eval ?q } ;

! CHR: eval-done @ // { Eval +nil+ } -- | ;
CHR: eval-step @ // { Eval L{ ?x . ?xs } } -- |
{ Eval1 ?x } { Eval ?xs } ;

! *** Literals
CHR: eval-lit @ // { Eval1 ?x } { Stack ?y } -- [ ?x callable-word? not ] |
{ Stack L{ W{ ?x } . ?y } } ;

! *** Executable word with known effect
! NOTE: destructive!
CHR: ensure-stack @ { Eval1 ?x } { Stack ?y } // -- [ ?x defined-effect :>> ?e ]
[ ?e in>> :>> ?i ] [ ?y llength* ?i length < ] |
[| | ?i elt-vars <reversed> >list ?rho lappend :> lin
 [ ?y lin ==! ] ] ;

! NOTE: destructive!
CHR: ensure-declare-stack @ { Eval1 declare } { Stack L{ A{ ?a } . ?r } } // -- [ ?a length :>> ?n ] |
[| | ?n [ f elt>var ] { } map-integers <reversed> >list ?rho lappend :> lin
 [ ?r lin ==! ]
] ;

! *** Shuffle Word Eval
! NOTE: depends on ensured stack
CHR: eval-shuffle @ // { Eval1 ?w } { Stack ?y } -- [ ?w "shuffle" word-prop :>> ?e ] |
[| | ?y ?e in>> length lcut :> ( top rest )
 top list>array <reversed> :> vin
 vin ?e shuffle <reversed> >list rest lappend :> sout
 { Stack sout }
] ;

! ** Expected Types at word inputs
CHR: eval-declare @ // { Eval1 declare } { Stack L{ A{ ?a } . ?r } } -- [ ?a <reversed> >list :>> ?tau ] |
{ Stack ?r }
{ ExpectType ?r ?tau } ;

CHR: math-types @ { Eval1 ?w } { Stack ?y } // -- [ ?w math-generic? ] [ ?w stack-effect in>> length number <array> >list :>> ?tau ] |
{ ExpectType ?y ?tau } ;

! ** Conditional execution

! ! Convert to typecase semantics
! ! FIXME
! CHR: eval-mux @ // { Eval1 ? } { Stack L{ ?q ?p ?c . ?rho } } -- |
! { Stack L{ ?x . ?rho } }
! { TypeCase ?x { ?c POSTPONE: f } ?p ?q } ;
! ! { Xor ?x { ?tau } { ?sig } }
! ! { DisjointMember ?tau ?x }
! ! { DisjointMember ?rho ?x }
! ! { Refine ?x { P{  } } }
! ! { C P{ Instance ?c  } }
! ! { TypeOf  }
! ! { TypeOf ?x P{   } }
! ! NOTE: should be outer-most-discriminator, but is coupled via vars...

! ** Higher-Order

! NOTE: This is call-site immediate: The types on the stack are
! _referenced_ by the expect declaration
CHR: call-defines-effect @ // { Eval1 call } { Stack L{ ?q . ?a } } -- |
{ ExpectType ?q P{ Effect ?a ?b f } }
{ Stack ?b } ;

CHR: dip-defines-effect @ // { Eval1 dip } { Stack L{ ?q ?x . ?a } } -- |
{ ExpectType ?q P{ Effect ?a ?b f } }
{ Stack L{ ?x . ?b } } ;

! ** Unknown Stuff
CHR: eval-any-call @ // { Eval1 ?w } { Stack ?a } -- [ ?w defined-effect :>> ?e ]
[ ?e in>> :>> ?i ]
[ ?e out>> :>> ?o ]
[ ?e bivariable-effect? [ "sig" utermvar ] [ ?a ?i length lcut nip ] if
  ?o elt-vars <reversed> >list swap lappend :>> ?b ]
|
! Really a marker for getting other word's stuff...
{ Exec ?w ?a ?b }
{ Stack ?b }
    ;

CHR: exec-known-word @ { TypeOf ?w ?e } // { Exec ?w ?a ?b } -- [ ?e Effect? ] |
! Trigger instantiation rule
{ ExpectType ?w P{ Effect ?a ?b f } } ;
! { ApplyEffect ?a ?b ?e } ;

CHR: exec-unknown-word @ { Exec ?w ?a ?b } // -- [ ?w generic? not ] [ ?w def>> :>> ?q ] |
{ InferEffect ?c ?rho ?sig ?q }
{ TypeOf ?w ?c }
    ;

! CHR: collect-inferred-word @ // { TypeOf ?c f } { C ?c P{ Effect ?rho ?sig } } -- |
! { TypeOf ?c P{ Effect ?rho ?sig } } ;


! ** Finishing
TUPLE: CloseEffect < chr-pred in ;

CHR: close-effect @ // { Effect ?rho __ f } { Eval +nil+ } P{ Stack ?sig } -- |
{ Effect ?rho ?sig f }
{ CloseEffect ?rho }
;

CHR: collect-type-pred @ { CloseEffect ?rho } // { Effect ?rho ?sig ?k } AS: ?p P{ ExpectType ?x __ } --
[ ?x term-var? ]
[ ?x ?rho vars ?sig vars union in? ]
[ ?k ?p suffix :>> ?l ]
|
{ Effect ?rho ?sig ?l } ;

CHR: finish-effect @ // { CloseEffect __ } -- | ;

! ** Cleanup
! CHR: dont-keep-literal-types @ // { TypeOf A{ ?q } __ } -- [ ?q callable? ] | ;

;

TERM-VARS: ?s0 ;

: bq ( code -- res )
    P{ Effect ?s0 f f }
    P{ Stack ?s0 }
    rot Eval boa 3array
    [ chr-stack swap run-chr-query store>> ] with-var-names ;
