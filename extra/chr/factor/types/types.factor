USING: chr chr.factor chr.factor.conditions chr.parser chr.state classes
classes.algebra kernel lists quotations terms ;

IN: chr.factor.types

! Statement: var has type
TUPLE: Type < val-pred type ;
TUPLE: Subtype < chr-pred sub super ;
TUPLE: Intersect < chr-pred tau sig ;
TUPLE: UnionType < chr-pred result member1 member2 ;
TUPLE: AcceptTypeUnion < AcceptType ;
TUPLE: ProvideTypeUnion < ProvideType ;
! TUPLE: AssumeTypes < chr-pred stack ;

! * Typing Judgments
! ** Instances and Types
! There is a distinction between the concept of "This value can be an instance of
! this type" and "A variable holding this value has to be declared this type? I
! suppose in straight-line code, especially without a subtyping relation this
! does not make any difference?

CHRAT: chrat-types { Type NotInstance Subtype Intersect }

CHR{ { Type ?x ?tau } // { Type ?x ?tau } -- | }
CHR: same-type @ { Type ?x ?tau2 } // { Type ?x ?tau1 } -- | [ ?tau1 ?tau2 ==! ] ;

CHR{ { AcceptType ?s ?x ?tau } // { AcceptType ?s ?x ?tau } -- | }

! Clean up
! TODO: make this val-preds?
! CHR{ { Dead ?x } // P{ Type ?x __ } -- | }

! CHR{ // { Type __ L{ } } -- | }
! CHR: destructure-type-head @ { Type L{ ?x . __ } L{ ?y . __ } } // -- | { Type ?x ?y } ;
! CHR: destructure-type-rest @ // { Type L{ __ . ?xs } L{ __ . ?ys } } -- | { Type ?xs ?ys } ;

! Analyze Stack types

! CHR: accept-type-from-stack @ // { AcceptTypes ?s ?x } -- { Stack ?s ?v } | { AcceptType ?s ?v ?x } ;
! CHR: accept-type-from-stack @ // { AcceptTypes ?s ?x } -- | { Stack ?s ?v } { AcceptType ?s ?v ?x } ;
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
CHR: lit-defines-type @ { Lit ?a ?b } // -- | [ ?a ?b class-of Type boa ] ;
! CHR: lit-defines-type @ { Lit ?a ?b } // -- | { Type ?a ?tau } [ ?tau class-of Subtype boa ] ;

CHR: accept-defines-type @ { AcceptType ?s ?x ?sig } // -- [ ?x known list? not ] | { Type ?x ?tau } { Cond ?s P{ Subtype ?tau ?sig } } ;

CHR: effects-are-callables @ { Effect ?x __ __ } { Type ?x ?tau } // -- |
{ Subtype ?tau callable } ;
! CHR: reject-type @ { AcceptType ?s ?x ?sig } // -- [ ?x known list? not ] |
! { Type ?x ?tau } { Cond P{ Not P{ Intersect ?tau ?sig } } P{ AbsurdState ?s } }  ;

! NOTE: Ideally, the condition system would cut intersections into separate conditions, e.g. a resulting reasoning like this:
! { AcceptType ?s ?x ?tau2 } => { Type ?x ?tau1 } => ∃ c1,c2:  c1 <=> { Intersect ?tau1 ?tau2 }, c2 ==> { ConflictState ?s }, { Disjoint c1 c2 }

! ** Algebra
CHR{ { Subtype ?x ?y } // { Subtype ?x ?y } -- | }
! CHR: instance-type @ P{ Instance ?x ?tau } // -- | P{ Type ?x ?tau } ; ! { Subtype ?tau1 ?tau } { Subtype ?tau ?tau1 } ;
CHR{ // { Subtype ?x ?y } -- [ ?x known classoid? ] [ ?y known classoid? ] | [ ?x ?y class<= [ f ] [ "Subtype Contradiction" throw ] if ] }

! ** Phi stuff
CHR: trivial-union @ // { UnionType ?tau3 ?tau1 ?tau1 } -- | [ ?tau3 ?tau1 ==! ] ;

CHR: builtin-union @ // { UnionType ?tau3 ?tau1 ?tau2 } -- [ ?tau1 classoid? ] [ ?tau2 classoid? ] |
[ ?tau3 ?tau1 ?tau2 class-or ==! ] ;

CHR: phi-types @ { Branch ?r __ ?c1 ?c2 } { Cond ?c1 P{ Type ?x ?tau1 } } { Cond ?c2 P{ Type ?x ?tau2 } } // -- |
{ Cond ?r P{ Type ?x ?tau3 } }
{ UnionType ?tau3 ?tau1 ?tau2 } ;

! * Condition Simplification
! CHR: answer-trivial-subtype @ // { ask { CheckTrivial P{ Subtype ?x ?y } } }
!  -- [ { [ ?x classoid? ] [ ?y classoid? ] } 0&& ]
! | { entailed { CheckTrivial P{ Subtype ?x ?y } } }
! [ { { [ ?x ?y class<= ] [ { IsTrivial P{ Subtype ?x ?y } } ] }
!     { [ ?x ?y classes-intersect? not ] [ { IsTrivial P{ Not P{ Subtype ?x ?y } } } ] }
!     [ f ]
!   } cond
! ] ;

 ! CHR: answer-trivial-subtype @ // { CheckTrivial P{ Subtype ?x ?y } }
 !  -- [ ?x classoid? ] [ ?y classoid? ]
 !  |
 ! [ { { [ ?x ?y class<= ] [ { IsTrivial P{ Subtype ?x ?y } } ] }
 !     { [ ?x ?y classes-intersect? not ] [ { IsTrivial P{ Not P{ Subtype ?x ?y } } } ] }
 !     [ f ]
 !   } cond
 ! ] ;
! CHR: trivial-subtypes @ { Subtype ?x ?y } // { Cond ?c P{ Subtype ?x ?y } } -- | { Cond +top+ P{ Subtype ?x ?y } } ;
CHR: known-subtypes @ // { Cond __ P{ Subtype ?x ?y } } -- [ ?x known ?y known class<= ] | ;
CHR: known-not-subtypes @ { Cond ?c P{ Subtype ?x ?y } } // -- [ ?x known ?y known classes-intersect? not ] | { Absurd ?c } ;
! CHR: type-known @ { Equiv ?c P{ Type ?x ?y } } // -- { Type ?x ?y } | { Trivial ?c } ;
CHR: type-known @ { Equiv ?c P{ Type ?x ?y } } { Type ?x ?y } // -- | { Trivial ?c } ;
! { Not P{ Subtype ?x ?y } }

! CHR: trivial-subtype-contradiction @ { Cond ?c { Subtype ?x ?y } } // --
! [ [ ? ] ]

! ** Stack Query

! CHR: foo @ { CondJump ?c ?c1} { Disjoint ?c1 ?c2 } { AcceptType ?c1 ?a ?tau1 } { AcceptType ?c2 ?a ?tau2 } //
! { UnionType ?tau3 ?tau2 ?tau1 }
! { AcceptType ?c  }

! CHR: answer-lit-notinstace @ { Lit ?x ?v } // { ask { NotInstance ?x ?tau } } -- [ ?v ?tau instance? not ] |
!      { entailed { NotInstance ?x ?tau } } ;

! CHR: answer-lit-instance @ { Lit ?x ?v } { AskAbout { Instance ?x ?tau } ?k ?vars } // -- [ ?v ?tau instance? ] |
! { AnswerAbout { Instance ?x ?tau } ?k ?vars } ;

! CHR: answer-no-lit-instance @ { Lit ?x ?v } { AskAbout { Instance ?x ?tau } ?k ?vars } // -- [ ?v ?tau instance? not ] |
! { AnswerAbout { Not { Instance ?x ?tau } } ?k ?vars } ;

;
