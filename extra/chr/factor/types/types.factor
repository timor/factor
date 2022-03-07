USING: arrays chr chr.comparisons chr.factor chr.factor.conditions chr.parser
chr.state classes classes.algebra classes.tuple kernel lists quotations terms ;

IN: chr.factor.types

! Statement: var has type
TUPLE: Type < val-pred type ;


TUPLE: type-pred < chr-pred type ;
INSTANCE: type-pred test-pred

TUPLE: Subtype < type-pred super ;
TUPLE: Intersect < type-pred sig ;
TUPLE: UnionType < type-pred member1 member2 ;
TUPLE: AcceptTypeUnion < AcceptType ;
TUPLE: ProvideTypeUnion < ProvideType ;
! TUPLE: AssumeTypes < chr-pred stack ;

! * Typing Judgments
! ** Instances and Types
! There is a distinction between the concept of "This value can be an instance of
! this type" and "A variable holding this value has to be declared this type? I
! suppose in straight-line code, especially without a subtyping relation this
! does not make any difference?

! NOTE: Type variables are assumed to be unique to the value variables!  This
! means that If a value with a type variable is dead, the type variable is also dead!
! In that sense, there is really not much of a difference between a type-pred
! and a val-pred...

CHRAT: chrat-types { Type NotInstance Subtype Intersect }

! *** Redundancies
CHR{ { Type ?x ?tau } // { Type ?x ?tau } -- | }
! NOTE: This is ground-term definition stuff.  Two different values can be made
! equal by branch simplification.  This has eager intersection semantics,
! i.e. it should be assumed that the more specific constraint was present in the
! first place.
CHR: same-atomic-type @ // { Type ?x A{ ?tau1 } } { Type ?x A{ ?tau2 } }
-- [ ?tau1 ?tau2 class-and :>> ?tau3 ] | { Type ?x ?tau3 } ;

CHR: same-type @ { Type ?x ?tau2 } // { Type ?x ?tau1 } -- | [ ?tau1 ?tau2 ==! ] ;

CHR{ { AcceptType ?s ?x ?tau } // { AcceptType ?s ?x ?tau } -- | }

! CHR: answer-known-type @ { is ?x ?tau } // { ask { Type ?y ?x } } -- | [ ?tau ?sig ==! ]
! { entailed { Type ?x ?sig } } ;

! Clean up
! TODO: make this val-preds?
! CHR{ { Dead ?x } // P{ Type ?x __ } -- | }

! CHR{ // { Type __ L{ } } -- | }
! CHR: destructure-type-head @ { Type L{ ?x . __ } L{ ?y . __ } } // -- | { Type ?x ?y } ;
! CHR: destructure-type-rest @ // { Type L{ __ . ?xs } L{ __ . ?ys } } -- | { Type ?xs ?ys } ;

! *** Early Simplifications
CHR: object-type-is-trivial @ // { Type ?x object } -- | ;
CHR: object-subtype-is-trivial @ // { Subtype ?x object  } -- | ;

! *** Expand Type Specifications
CHR: accept-type-from-stack @ // { AcceptTypes ?s ?x } -- [ ?x known :>> ?l list? ] [ ?l list>stack :>> ?v ] |
{ Stack ?s ?v } { AcceptType ?s ?v ?l } ;
! CHR{ // { AcceptType __ ?v object } -- | }
CHR{ // { AcceptType __ __ L{ } } -- | }
CHR: destructure-accept-type-head @ { AcceptType ?s L{ ?x . ?xs } L{ ?y . ?ys } } // -- | { AcceptType ?s ?x ?y } ;
CHR: destructure-accept-type-rest @ // { AcceptType ?s L{ ?x . ?xs } L{ ?y . ?ys } } -- | { AcceptType ?s ?xs ?ys } ;

CHR: provide-type-from-stack @ // { ProvideTypes ?s ?x } -- { Stack ?s ?v } | { ProvideType ?s ?v ?x } ;
CHR{ // { ProvideType __ ?v object } -- | }
CHR{ // { ProvideType __ __ L{ } } -- | }
! CHR: destructure-provide-type @ // { ProvideType ?s L{ ?x . ?xs } L{ ?y . ?ys } } -- | { ProvideType ?s ?x ?y } { ProvideType ?s ?xs ?ys } ;
CHR: destructure-provide-type-head @ { ProvideType ?s L{ ?x . ?xs } L{ ?y . ?ys } } // -- | { ProvideType ?s ?x ?y } ;
CHR: destructure-provide-type-rest @ // { ProvideType ?s L{ ?x . ?xs } L{ ?y . ?ys } } -- | { ProvideType ?s ?xs ?ys } ;

! CHR: lit-is-instance @ { Lit ?a ?b } // -- | [ ?a ?b class-of Instance boa ] ;
! CHR: lit-defines-type @ { Lit ?a ?b } // -- | [ ?a ?b class-of Type boa ] ;
! CHR: lit-defines-type @ { Lit ?a ?b } // -- | { Type ?a ?tau } [ ?tau class-of Subtype boa ] ;
! CHR: sane-lit-types @ { is ?x A{ ?v } } { Type ?x A{ ?tau } } // -- | [ ?v ?tau instance? [ f ] [ ?v ?tau "lit type collision" 3array throw ] if ] ;
! CHR: lit-defines-type @ { is ?x A{ ?v } } // { Type ?x ?tau } -- [ ?tau known term-var? ] | [ ?x ?v class-of Type boa ] ;
CHR: lit-defines-type @ { is ?x A{ ?v } } { Type ?x ?tau } // -- [ ?tau known term-var? ] | [ ?tau ?v class-of ==! ] ;


! NOTE: This must provide subtype definitions, otherwise we claim to know what the declared type of the input variable is supposed to be
CHR: accept-defines-type @ // { AcceptType ?s ?x ?tau } -- [ ?x known list? not ] | { --> ?s P{ Type ?x ?sig } } P{ Subtype ?sig ?tau } ;

! XXX not sure if this is correct, do we also need subtype reasoning here?
! ... pretty sure we do... final-tests should then narrow stuff down...
! CHR: provide-defines-type @ // { ProvideType ?s ?x ?tau } -- [ ?x known list? not ] | { --> ?s P{ Type ?x ?tau } } ;
CHR: provide-defines-type @ // { ProvideType ?s ?x ?tau } -- [ ?x known list? not ] | { --> ?s P{ Type ?x ?sig } } P{ Subtype ?sig ?tau } ;

CHR: effects-are-callables @ { Effect ?x __ __ } { Type ?x ?tau } // -- |
{ Subtype ?tau callable } ;
! CHR: reject-type @ { AcceptType ?s ?x ?sig } // -- [ ?x known list? not ] |
! { Type ?x ?tau } { Cond P{ Not P{ Intersect ?tau ?sig } } P{ AbsurdState ?s } }  ;

! NOTE: Ideally, the condition system would cut intersections into separate conditions, e.g. a resulting reasoning like this:
! { AcceptType ?s ?x ?tau2 } => { Type ?x ?tau1 } => ∃ c1,c2:  c1 <=> { Intersect ?tau1 ?tau2 }, c2 ==> { ConflictState ?s }, { Disjoint c1 c2 }

! ** Literal Handling
! CHR: import-ground-types @ { is ?x A{ ?sig } } { Type ?x ?tau } // -- | { Type ?x ?sig } ;
CHR: import-literal-types-test @ { is ?c A{ ?tau } } // { --> P{ Type ?x ?c } ?q } -- | { --> P{ Type ?x ?tau } ?q } ;
CHR: import-literal-neg-types-test @ { is ?c A{ ?tau } } // { \--> P{ Type ?x ?c } ?q } -- | { \--> P{ Type ?x ?tau } ?q } ;
CHR: import-literal-not-types @ { is ?c A{ ?tau } } // { Not P{ Type ?x ?c } } -- | { Not P{ Type ?x ?tau } } ;
! CHR: literal-must-be-instance @ // { Type A{ ?v } A{ ?c } } -- |
! CHR: literal-must-be-instance @ // { Type A{ ?v } A{ ?c } } -- |
! CHR: literal-must-be-instance @ { eq ?x A{ ?v } } // { Type ?x A{ ?c } } -- |
! [ ?v ?c instance? [ f ] [ ?x ?v ?c 3array "inconsistent lit types" throw ] if ] ;

! CHR: literal-sets-type-constant @ // { Type A{ ?v } ?tau } -- | [ ?tau ?v class-of ==! ] ;

CHR: check-literal-accept-type @ // { AcceptType __ A{ ?v } A{ ?tau } }
-- [ ?v ?tau instance? ] | ;

CHR: literal-sets-query-type-constant @ { is ?tau A{ ?sig } } { Equiv __ P{ Type __ ?tau } } // -- | [ ?tau ?sig ==! ] ;

CHR: literal-defines-type @ { --> ?c P{ is ?x A{ ?v } } } //
-- [ ?v class-of :>> ?sig ] | { --> ?c P{ Type ?x ?sig } }
! { --> ?c P{ Subtype ?tau ?sig } }
    ;

CHR: reduntant-atomic-type-restriction @ { Type ?x A{ ?tau } } // { Not P{ Type ?x A{ ?sig } } } -- [ ?tau ?sig classes-intersect? not ] | ;

! ** Algebra
CHR{ { Subtype ?x ?y } // { Subtype ?x ?y } -- | }
! CHR: instance-type @ P{ Instance ?x ?tau } // -- | P{ Type ?x ?tau } ; ! { Subtype ?tau1 ?tau } { Subtype ?tau ?tau1 } ;
CHR{ // { Subtype A{ ?x } A{ ?y } } -- | [ ?x ?y class<= [ f ] [ "Subtype Contradiction" throw ] if ] }
! CHR{ // { Type A{ ?x } ?y } -- [ ?y known classoid? ] | [ ?x ?y known instance? [ f ] [ "Subtype Contradiction" throw ] if ] }
CHR{ // { Type A{ ?x } A{ ?y } } -- | [ ?x ?y instance? [ f ] [ "Type Contradiction" throw ] if ] }


CHR: intersect-known-subtypes @ // { Subtype ?x A{ ?sig } } { Subtype ?x A{ ?tau } } -- [ ?sig ?tau class-and :>> ?tau3 ] |
{ Subtype ?x ?tau3 } ;


CHR: cannot-be-subtype @ { Type ?x ?tau } { Subtype ?tau A{ ?tau1 } } //
{ --> ?c1 P{ Type ?x A{ ?tau2 } } } -- [ ?tau1 ?tau2 classes-intersect? not ] | { Impossible ?c1 } ;

CHR: redundant-exclusions @ { Type ?x ?c } { Subtype ?c A{ ?tau } } // { Not P{ Type ?x A{ ?sig } } } --
[ ?tau ?sig classes-intersect? not ] | ;

! CHR: no-final-subtypes @ { Type ?x ?tau } // { Subtype ?tau A{ ?c } } -- [ ?c final-class? ] |
! [ ?tau ?c ==! ] ;

! ** Phi stuff
CHR: trivial-union @ // { UnionType ?tau3 ?tau1 ?tau1 } -- | [ ?tau3 ?tau1 ==! ] ;
CHR: reflexive-union @ { UnionType ?tau3 ?tau1 ?tau2 } // { UnionType ?tau3 ?tau2 ?tau1 } -- | ;

CHR: builtin-union @ // { UnionType ?tau3 A{ ?tau1 } A{ ?tau2 } } -- |
[ ?tau3 ?tau1 ?tau2 class-or ==! ] ;

CHR: data-phi-types @ { EitherOr ?c __ ?c1 ?c2 }
{ --> ?c1 P{ is ?x ?a } } { --> ?c1 P{ Type ?a ?tau1 } }
{ --> ?c2 P{ is ?x ?b } } { --> ?c2 P{ Type ?b ?tau2 } }
// -- |
{ --> ?c P{ Type ?x ?tau3 } }
{ UnionType ?tau3 ?tau1 ?tau2 } ;

CHR: data-phi-direct-types @ { EitherOr ?c __ ?c1 ?c2 }
{ --> ?c1 P{ Type ?a ?tau1 } }
{ --> ?c2 P{ Type ?a ?tau2 } } // -- |
{ --> ?c P{ Type ?a ?tau3 } }
{ UnionType ?tau3 ?tau1 ?tau2 } ;


! CHR: data-phi-types @ { EitherOr ?c ?c1 ?c2 }
! { --> ?c1 P{ is ?x ?a } } P{ Type ?a ?tau1 }
! { --> ?c2 P{ is ?x ?b } } P{ Type ?b ?tau2 }
! // -- |
! P{ Type ?x ?tau3 }
! { UnionType ?tau3 ?tau1 ?tau2 } ;

! CHR: assume-gradual-type @
! { Type ?x ?tau1 }
! { --> ?c1 P{ Type ?x ?tau2 } }  // -- [ ?tau1 known term-var? ] |
! { UnionType ?tau1 ?tau2 ?tau3 } ;

! ! ** Comparison implications
! CHR: eq-implies-subtype @ AS: ?a <={ Cond ?c P{ = ?x ?v } } // -- [ ?v known? ] |
! [| | ?v class-of :> tau
!  ?a clone ?v class-of ?x swap Type boa >>implied
!  ! { Cond ?c P{ Type ?x tau } }
! ] ;

! * Condition Handling
CHR: known-not-subtype @ // { --> ?c P{ Subtype A{ ?tau } A{ ?sig } } } -- |
[ ?tau ?sig class<= [ f ] [ { Impossible ?c } ] if ] ;

CHR: cond-same-type @ { --> ?c P{ Type ?x ?tau } } // { --> ?c P{ Type ?x ?sig } } -- | [ ?sig ?tau ==! ] ;

! NOTE: again intersection semantics on IDENTICAL Values, i.e. the constraint
! set must be consistent
CHR: global-atomic-type-known @ // { Type ?x A{ ?tau1 } } { Type ?x A{ ?tau2 } } -- [ ?tau1 ?tau2 class-and :>> ?tau3 ] |
{ Type ?x ?tau3 } ;

CHR: impossible-by-atomic-type-conflict @ { Type ?x A{ ?tau1 } } { --> ?q P{ Type ?x A{ ?tau2 } } } // -- [ ?tau1 ?tau2 classes-intersect? not ] |
{ Impossible ?q } ;

CHR: redundant-by-atomic-type-conflict @ { Type ?x A{ ?tau1 } } // { --> P{ Type ?x A{ ?tau2 } } __ } -- [ ?tau1 ?tau2 classes-intersect? not ] | ;

! FIXME: this is actually an inconsistency test!
! CHR: global-type-known @ { Type ?x ?tau } { --> __ P{ Type ?x ?sig } } // -- | [ ?sig ?tau ==! ] ;

! ** Builtin Defaults
CHR: boolean-not-false-must-be-true @
{ Type ?x boolean } // { Not P{ is ?x W{ f } } } -- | { is ?x t } ;

! TODO: this should probably be made by converting to a union-type statement and erasing!
! CHR: not-fixnum-is-bignum @ { Not P{ Type ?x fixnum } } // { Type ?x integer } -- | { Type ?x bignum } ;
! CHR: not-bignum-is-fixnum @ { Not P{ Type ?x bignum } } // { Type ?x integer } -- | { Type ?x fixnum } ;


;
