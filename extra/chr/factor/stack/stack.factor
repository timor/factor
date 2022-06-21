USING: accessors arrays chr chr.factor chr.factor.defs chr.parser chr.state
classes classes.algebra combinators.short-circuit effects generic kernel
kernel.private lists math math.parser quotations sequences sets strings terms
types.util words words.symbol ;

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
TUPLE: InferEffect < chr-pred thing in out def ;
TUPLE: Inferred < chr-pred thing start ;

! Housekeeping during subordinate inference (GC roots style...)
TUPLE: Parms < chr-pred list ;

! Closure-Calculus style...?
! Semantics: If this is present, it means that when the effect is built, a second variant needs to be built in addition
TUPLE: Variants < chr-pred var cases ;
TUPLE: Variant < chr-pred var type binds ;
TUPLE: Case < chr-pred var type ;

TUPLE: MakeVariant < chr-pred effect binds ;

! Aliases through branches
TUPLE: Copy from to ;
! Types

! Definition
TUPLE: Type < chr-pred var type ;
TUPLE: Or < chr-pred type1 type2 ;
TUPLE: And < chr-pred type1 type2 ;
TUPLE: Xor < chr-pred type1 type2 ;
TUPLE: Not < chr-pred type ;

! Non-directional
TUPLE: Mux < chr-pred cond then else ;
TUPLE: Demux < chr-pred cond then else ;
! TUPLE: Variant < chr-pred var1 val1 var2 val2 ;

! Return-directional
TUPLE: Phi < chr-pred res in1 in2 ;

! Effect Type
TUPLE: Effect < chr-pred in out preds ;
TUPLE: EffectAnd < chr-pred effect1 effect2 ;

: effect-vars ( Effect -- vars )
    [ in>> vars ] [ out>> vars ] bi union ;

! Type of "expressions"
TUPLE: TypeOf < chr-pred thing type ;

! Refined Type Stuff
TUPLE: TypeLet < chr-pred var type preds ;
TUPLE: Refine < chr-pred type preds ;

! Typecase
TUPLE: TypeCase < chr-pred var cond then else ;

! Predicate defs
TUPLE: Pred < chr-pred var expr ;
! Simplest predicate
TUPLE: Instance < chr-pred var type ;
TUPLE: Declare < chr-pred stack types ;

! Expresses that the types on the stack must be subtypes of the list of types in types, which is done
! typically at word calls, e.g. for +
! i.e. { ExpectType L{ ?x1 ?x2 . ?rho } { number number } }
TUPLE: ExpectType < chr-pred stack types ;
! Blocking
TUPLE: Sub < chr-pred stack types ;

TUPLE: IfTe < chr-pred bool then else ;
! TUPLE: DisjointMember < chr-pred type union ;

! Arithmetic Sub-Solver
TUPLE: Sum < chr-pred result x y ;


! Embedded Reasoning
TUPLE: --> cond type ;

CHRAT: chr-stack { }

! ** Type stack operations

! *** Early reasoning
CHR: unique-instance @ { Instance ?x ?tau } // { Instance ?x ?tau } -- | ;

! *** Destructuring
CHR: did-expect-types @ // { ExpectType __ +nil+ } -- | ;
CHR: expecting-types @ // { ExpectType L{ ?x . ?xs } L{ ?y . ?ys } } -- |
{ ExpectType ?x ?y }
{ ExpectType ?xs ?ys } ;

! CHR: catch-expand-recursive-types-right @ // { ExpectType L{ ?x . ?xs } ?y } -- [ ?y ?xs lastcdr = ] | ;
! Above is too late, so we do this expensive test before substitution...
CHR: catch-expand-recursive-types-right @ // { ExpectType L{ ?x . ?xs } ?y } --
[ [ ?y ?xs solve-eq not ] no-var-restrictions ] | ;

! Simplify muxed types
CHR: same-mux-type-right @ // { ExpectType ?x P{ Mux ?c ?y ?y } } -- |
{ ExpectType ?x ?y } ;

! NOTE: destructive
CHR: expand-expect-types-right @ // { ExpectType L{ ?x . ?xs } ?b } -- [ ?b term-var? ]
! Cheapo test
! [ ?b ?xs lastcdr = not ]
! Not so cheapo test
! [| | "y" utermvar :> y
!  "ys" utermvar :> ys
!  [ { { ?b L{ y . ys } } { L{ ?x . ?xs } L{ y . ys } } } solve-problem dup . ] no-var-restrictions ]
|
[ ?b L{ ?y . ?ys } ==! ]
{ ExpectType ?xs ?ys }
{ ExpectType ?x ?y }
    ;

! NOTE: destructive
CHR: expand-expect-mux-types-right @ // { ExpectType P{ Mux ?c L{ ?x . ?xs } L{ ?y . ?ys } } ?b } -- |
! TODO: order matters?
[ ?b L{ ?z . ?zs } ==! ]
{ ExpectType P{ Mux ?c ?xs ?ys } ?zs }
{ ExpectType P{ Mux ?c ?x ?y } ?z } ;

CHR: catch-expand-recursive-types-left @ // { ExpectType ?a L{ ?y . ?ys } } --
[ [ ?a ?ys solve-eq not ] no-var-restrictions ] | ;

! Left
CHR: expand-expect-types-left @ // { ExpectType ?a L{ ?y . ?ys } } -- [ ?a term-var? ] |
! [ ?a L{ ?x . ?xs } ==! ]
[ L{ ?x . ?xs } ?a ==! ]
{ ExpectType ?xs ?ys }
{ ExpectType ?x ?y }
    ;

! NOTE: destructive
CHR: expand-expect-mux-types-left @ // { ExpectType ?a P{ Mux ?c L{ ?x . ?xs } L{ ?y . ?ys } } } -- [ ?a term-var? ] |
! TODO: order matters?
[ L{ ?z . ?zs } ?a ==! ]
{ ExpectType ?zs P{ Mux ?c ?xs ?ys } }
{ ExpectType ?z P{ Mux ?c ?x ?y } } ;

! CHR: destructure-expect-mux-types-left @ // { ExpectType L{ ?z . ?zs } P{ Mux ?c L{ ?x . ?xs } L{ ?y . ?ys } } } -- |
! { ExpectType ?zs P{ Mux ?c ?xs ?ys } }
! { ExpectType ?z P{ Mux ?c ?x ?y } } ;


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

! *** Intersection Effect types
! CHR: expect-mux-lhs @ // { ExpectType P{ Mux ?c ?x ?y } P{ Effect ?a ?b ?l } } -- |
! [| | P{ Effect ?a ?b ?l } :> eff
!  eff ?c vars fresh-without [ { { ?c ?x } } lift ] no-var-restrictions :> e1
!  eff ?c vars fresh-without [ { { ?c ?y } } lift ] no-var-restrictions :> e2
!  e1 [ in>> ] [ out>> ] bi :> ( in1 out1 )
!  e2 [ in>> ] [ out>> ] bi :> ( in2 out2 )
!  {
!      ! [ in1 in2 ==! ]
!      P{ ExpectType ?x e1 }
!      P{ ExpectType ?y e2 }
!      P{ ExpectType ?a P{ Mux ?c in1 in2 } }
!      P{ ExpectType P{ Mux ?c out1 out2 } ?b }
!  }
! ] ;

CHR: expect-mux-lhs @ // { ExpectType P{ Mux ?c ?x ?y } P{ Effect ?a ?b ?l } } -- |
[| |
 P{ Effect ?a ?b ?l } :> eff
 eff ?c vars fresh-without [ { { ?c ?x } } lift ] no-var-restrictions :> e1
 eff ?c vars fresh-without [ { { ?c ?y } } lift ] no-var-restrictions :> e2
 e1 [ in>> ] [ out>> ] bi :> ( in1 out1 )
 e2 [ in>> ] [ out>> ] bi :> ( in2 out2 )
 {
     ! [ in1 in2 ==! ]
     P{ ExpectType ?x e1 }
     P{ ExpectType ?y e2 }
     P{ ExpectType ?a P{ Mux ?c in1 in2 } }
     P{ ExpectType P{ Mux ?c out1 out2 } ?b }
 }
] ;


! *** Instantiate "type scheme" when we expect a literal to fulfill an effect
! Semantics: We expect the singleton type of a callable to fulfill some (call-site)
! effect spec for quotations
CHR: already-inferred-effect @ { TypeOf ?q ?tau } // { ExpectType A{ ?q } P{ Effect ?a ?b ?k } } -- [ ?tau Effect? ] |
[| | ?tau [ in>> ] [ out>> ] [ preds>> ] tri :> ( in out preds )
 ! Only instantiate binders
 ! ?tau in vars out vars union fresh-with :> inst
 ! Instantiate all locals
 ?tau fresh :> inst
 { ExpectType inst P{ Effect ?a ?b ?k } }
] ;

! *** Trigger inference of unknown quot
! FIXME: This could just be a symptom cure for not creating intersection arrows early enough!
! XXX: Nope, didnt help...
CHR: infer-only-once @ { TypeOf ?q ?c } // { InferEffect ?d __ __ ?q } { TypeOf ?q ?d } -- | ;

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

! This gets rid of diamonds
! CHR: expect-transitive-expr-is-same @ P{ ExpectType ?a ?x } // P{ ExpectType ?x ?b } -- [ ?x ground-value? not ] |
! { ExpectType ?a ?b } ;
CHR: simplify-diamond @ // P{ ExpectType ?a P{ Mux ?c ?x ?y } } P{ ExpectType P{ Mux ?c ?x ?y } ?b } -- [ ?a term-var? ] [ ?b term-var? ] |
[ ?a ?b ==! ] ;


! ** Subordinate inference
CHR: merge-parms @ // { Parms ?a } { Parms ?b } -- [ ?a ?b union :>> ?c ] | { Parms ?c } ;


CHR: do-sub-infer-effect @ // { InferEffect ?c ?rho ?sig ?q } { Eval ?p } { Effect ?a A{ f } ?k } { Stack ?b } { Parms ?l } -- |
{ Effect ?rho f f }
{ Parms f }
{ Stack ?rho }
{ Eval ?q }
{ Inferred ?c ?rho }
{ Effect ?a f ?k }
{ Parms ?l }
{ Stack ?b }
{ Eval ?p } ;

CHR: collect-sub--effect @ // { Inferred ?c ?rho } { Effect ?rho ?sig ?k } -- |
[ ?c P{ Effect ?rho ?sig ?k } ==! ] ;


! ** Stack-state advancing

CHR: do-declare @ { Stack ?s } // { Declare f ?l } -- |
{ Declare ?s ?l } ;
CHR: did-declare @ // { Declare __ +nil+ } -- | ;
CHR: destructure-declare @ // { Declare L{ ?x . ?xs } L{ ?y . ?ys } } -- |
{ Declare ?xs ?ys }
{ Instance ?x ?y } ;


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
! NOTE: exclude inline words
CHR: ensure-stack @ { Eval1 ?x } { Stack ?y } // --
! [ ?x inline? not ]
[ ?x { [ \ ? eq? ] [ inline? not ] } 1|| ]
[ ?x defined-effect :>> ?e ]
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
{ Declare f ?tau } ;
! { ExpectType ?r ?tau } ;

! CHR: math-types @ { Eval1 ?w } { Stack ?y } // -- [ ?w math-generic? ] [ ?w stack-effect in>> length number <array> >list :>> ?tau ] |
! { ExpectType ?y ?tau } ;
CHR: input-classes @ { Eval1 ?w } { Stack ?y } // -- [ ?w "input-classes" word-prop dup [ <reversed> >list ] when :>> ?tau ] |
{ ExpectType ?y ?tau } ;

! ** Conditional execution

! ! Convert to typecase semantics
! ! FIXME
! CHR: eval-mux-parms @ // { Eval1 ? } { Stack L{ ?q ?p ?c . ?rho } } -- |
! { Parms { ?x } }
! { Parms { ?v } }
! { Stack L{ ?v . ?rho } }
! { Type ?v P{ Mux ?c ?p ?q } }
!     ;

! CHR: eval-mux @ // { Eval1 ? } { Stack L{ ?q ?p ?c . ?rho } } -- |
! { Stack L{ P{ Mux ?c ?p ?q } . ?rho } }
!     ;
! CHR: eval-mux-variant @ // { Eval1 ? } { Stack L{ ?q ?p ?c . ?rho } } -- |
! { Stack L{ ?v . ?rho } }
! { Variants ?c { { W{ f } { { ?v ?q } } }
!                 { not{ W{ f } } { { ?v ?p } } } } }
!     ;

! CHR: eval-mux-chr-or @ // { Eval1 ? } { Stack L{ ?q ?p ?c . ?rho } } -- |
! Cond{ { P{ Case ?c W{ f } }
!            { P{ Stack L{ ?q . ?rho } } } }
!       { P{ Case ?c not{ W{ f } } }
!           { P{ Stack L{ ?p . ?rho } } } }
!       } ;

! NOTE: destructive
! CHR: eval-mux-stack @ // { Eval1 ? } { Stack L{ ?q ?p ?c . ?rho } } -- |
! [ ?c { { W{ f } ?k }
!         { not{ W{ f } } ?l } }
!      ==! ]
! { Stack L{ { { ?q ?k } { ?p ?l } } . ?rho } } ;

! CHR: eval-mux-type @ // { Eval1 ? } { Stack L{ ?q ?p ?c . ?rho } } -- |
! { Stack ?v . ?rho }
! { Instance ?c  }


! CHR: eval-if @ // { Eval1 if } { Stack L{ ?q ?p ?c . ?rho } } -- |
! { ExpectType ?p P{ Effect ?rho ?sig { P{ ExpectType ?d not{ POSTPONE: f } } } } }
! { ExpectType ?q P{ Effect ?rho ?sig { P{ ExpectType ?e POSTPONE: f } } } }
! { ExpectType ?c }
! { Stack ?sig } ;

! ** Higher-Order

! NOTE: This is call-site immediate: The types on the stack are
! _referenced_ by the expect declaration
! Semantics: We expect the quotation effect to fulfill the type expectations of a hypothetical effect at the call site.
! Thus, the given arrow type must be a subtype of the call-site-expected arrow type.
! Together with input contravariance and output variance, this means:
! - The set of values provided to the called effect as input must be a subset of the set of values the effect is define on.
! - The set of values returned by the called effect as output must be a subset of the set of values expected by the continuation.
CHR: call-defines-effect @ // { Eval1 call } { Stack L{ ?q . ?a } } -- |
{ ExpectType ?q P{ Effect ?a ?b f } }
{ Stack ?b } ;

CHR: dip-defines-effect @ // { Eval1 dip } { Stack L{ ?q ?x . ?a } } -- |
{ ExpectType ?q P{ Effect ?a ?b f } }
{ Stack L{ ?x . ?b } } ;

! ** Unknown Stuff
CHR: eval-inline-call @ // { Eval1 ?w } { Stack ?a } -- [ ?w inline? ]
[ ?w \ ? eq? not ]
|
{ Exec ?w ?a ?b }
{ Stack ?b } ;

! CHR: default-output-classes @ { Eval1 ?w } // -- [ ?w "default-output-classes" word-prop :>> ?c ] [ ?c <reversed> >list :>> ?tau ] |
! { Declare f ?tau } ;

! NOTE: depends on ensured stack
CHR: eval-any-call @ // { Eval1 ?w } { Stack ?a } -- [ ?w defined-effect :>> ?e ]
[ ?e in>> :>> ?i ]
[ ?e out>> :>> ?o ]
[ ?e bivariable-effect? [ "sig" utermvar ] [ ?a ?i length lcut nip ] if
  ?o elt-vars <reversed> >list swap lappend :>> ?b ]
|
! Really a marker for getting other word's stuff...
{ Exec ?w ?a ?b }
[ ?w "default-output-classes" word-prop dup
  [
      <reversed> >list ?b swap Declare boa
  ] when
]
{ Stack ?b }
    ;

CHR: exec-known-word @ { TypeOf ?w ?e } // { Exec ?w ?a ?b } -- ! [ ?e Effect? ]
|
! Trigger instantiation rule
{ ExpectType ?w P{ Effect ?a ?b f } } ;

PREDICATE: self-defined < word [ 1quotation ] [ def>> ] bi = ;


CHR: exec-unknown-word @ { Exec ?w ?a ?b } // -- [ ?w generic? not ] [ ?w def>> :>> ?q ]
[ ?w self-defined? not ]
|
{ InferEffect ?c ?rho ?sig ?q }
{ TypeOf ?w ?c }
    ;

! ** Finishing
TUPLE: CloseEffect < chr-pred in ;

CHR: close-effect @ // { Effect ?rho __ f } { Eval +nil+ } P{ Stack ?sig } -- |
{ Effect ?rho ?sig f }
{ CloseEffect ?rho }
;

! *** Rebuild Variants
CHR: combine-variant @ // { Variant ?x ?tau ?k } { Variant ?x ?tau ?l } -- [ ?k ?l union :>> ?m ] |
{ Variant ?x ?tau ?m } ;

CHR: make-variant-merge @ { CloseEffect ?rho } AS: ?e P{ Effect ?rho __ __ } // { ExpectType P{ Mux ?c ?a ?b } ?x } --
[ ?x ?e effect-vars in? ] |
{ Variant ?c W{ f } { { ?a ?x } } }
{ Variant ?c not{ W{ f } } { { ?b ?x } } } ;

CHR: make-variant-split @ { CloseEffect ?rho } AS: ?e P{ Effect ?rho __ __ } // { ExpectType ?x P{ Mux ?c ?a ?b } } --
[ ?x ?e effect-vars in? ] |
{ Variant ?c W{ f } { { ?x ?a } } }
{ Variant ?c not{ W{ f } } { { ?x ?b } } } ;

! *** Collect invariant results
UNION: body-pred ExpectType Instance ;
CHR: collect-type-pred @ { CloseEffect ?rho } // { Effect ?rho ?sig ?k } AS: ?p <={ body-pred ?x __ } --
! [ ?x term-var? ]
! [ ?x ?rho vars ?sig vars union in? ]
[ ?x vars empty? not ]
[ ?x vars ?rho vars ?sig vars union subset? ]
[ ?k ?p suffix :>> ?l ]
|
{ Effect ?rho ?sig ?l } ;

! *** Do Variants

CHR: prepare-variant-effect @ { CloseEffect ?rho } // AS: ?e P{ Effect ?rho __  __ } { Variant ?c ?tau ?l } -- [ ?l ?c ?tau 2array prefix :>> ?k ] |
[ ?e ]
{ MakeVariant ?e ?k } ;

CHR: remove-variant-original @ { CloseEffect ?rho } { MakeVariant ?e __ } // AS: ?e P{ Effect ?rho __ __ } -- | ;

! *** Propagate Conditional Reasoning
! NOTE: will escalate with recursive conditional datatypes
! CHR: make-variant @ { CloseEffect ?rho } AS: ?e P{ Effect ?rho ?sig ?k } // { Variant ?v ?tau ?l } --
! [ ?v ?e effect-vars in? ] |
! [ ?e ?l { ?v ?tau } suffix lift ] ;

! CHR: make-variants @ { CloseEffect ?rho } // AS: ?e P{ Effect ?rho ?sig ?k } { Variants ?v ?l } --
! [ ?v ?e effect-vars in? ] |
! [ ?l [| type binds |
!       ?v type 2array binds swap suffix
!       ?e swap lift
!      ] { } assoc>map ] ;


! *** Collect house-keepers
CHR: collect-parms @ { CloseEffect __ } // { Parms __ } -- | ;
CHR: finish-effect @ // { CloseEffect __ } -- | ;

! ** Cleanup
! CHR: dont-keep-literal-types @ // { TypeOf A{ ?q } __ } -- [ ?q callable? ] | ;

;

TERM-VARS: ?s0 ;

: bq ( code -- res )
    P{ Effect ?s0 f f }
    P{ Stack ?s0 }
    rot Eval boa 3array
    P{ Parms f } prefix
    [ chr-stack swap run-chr-query store>> ] with-var-names ;
