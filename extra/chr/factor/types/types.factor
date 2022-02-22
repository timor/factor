USING: chr chr.factor chr.factor.conditions chr.parser chr.state classes kernel
lists terms ;

IN: chr.factor.types

! Statement: var has type
TUPLE: Type < chr-pred val type ;
TUPLE: Subtype < chr-pred sub super ;
TUPLE: UnionType < chr-pred result member1 member2 ;
TUPLE: AcceptTypeUnion < AcceptType ;
TUPLE: ProvideTypeUnion < ProvideType ;
! TUPLE: AssumeTypes < chr-pred stack ;

CHRAT: chrat-types { NotInstance }

CHR{ { Type ?x ?tau } // { Type ?x ?tau } -- | }
CHR: same-type @ { Type ?x ?tau2 } // { Type ?x ?tau1 } -- | [ ?tau1 ?tau2 ==! ] ;

CHR{ { AcceptType ?s ?x ?tau } // { AcceptType ?s ?x ?tau } -- | }

! Clean up
! TODO: make this val-preds?
CHR{ { Dead ?x } // P{ Type ?x __ } -- | }

! Analyze Stack types

CHR: accept-type-from-stack @ { Stack ?s ?v } // { AcceptTypes ?s ?x } -- | { AcceptType ?s ?v ?x } ;
CHR{ // { AcceptType __ ?v object } -- | }
CHR{ // { AcceptType __ __ L{ } } -- | }
CHR: destructure-accept-type @ // { AcceptType ?s L{ ?x . ?xs } L{ ?y . ?ys } } -- | { AcceptType ?s ?x ?y } { AcceptType ?s ?xs ?ys } ;

CHR: provide-type-from-stack @ { Stack ?s ?v } // { ProvideTypes ?s ?x } -- | { ProvideType ?s ?v ?x } ;
CHR{ // { ProvideType __ ?v object } -- | }
CHR{ // { ProvideType __ __ L{ } } -- | }
CHR: destructure-provide-type @ // { ProvideType ?s L{ ?x . ?xs } L{ ?y . ?ys } } -- | { ProvideType ?s ?x ?y } { ProvideType ?s ?xs ?ys } ;

CHR: lit-is-instance @ { Lit ?a ?b } // -- | [ ?a ?b class-of Instance boa ] ;

CHR: accept-lit-type @ { Lit ?x ?v } // { AcceptType __ ?x ?tau } -- [ ?v ?tau instance? ] | ;
CHR: reject-lit-type @ { Lit ?x ?v } // { AcceptType ?s ?x ?tau } -- [ ?v ?tau instance? not ] |
     { ConflictState ?s { Lit ?x ?v } { AcceptType ?s ?x ?tau } } ;

! ** Algebra
! CHR: combine-union-accept @ // { AcceptTypeUnion ?c ?x ?tau1 } { AcceptTypeUnion ?c ?x ?tau2 } -- |
! [| | ?tau1 ?tau2 union :> tau3 { AcceptTypeUnion ?c ?x tau3 } ] ;

! CHR: combine-union-provide @ // { ProvideTypeUnion ?c ?x ?tau1 } { ProvideTypeUnion ?c ?x ?tau2 } -- |
! [| | ?tau1 ?tau2 union :> tau3 { ProvideTypeUnion ?c ?x tau3 } ] ;

! ! TODO: can we make this generic?
! CHR: propagate-accept-type @ { AcceptType ?c1 ?x ?tau } { CondJump ?c ?c1 } // -- | { AcceptTypeUnion ?c ?x { ?tau } } ;
! CHR: propagate-provide-type @ { ProvideType ?c1 ?x ?tau } { CondJump ?c ?c1 } // -- | { ProvideTypeUnion ?c ?x { ?tau } } ;
! CHR: propagate-accept-union @ { CondJump ?c ?c1 } { AcceptTypeUnion ?c1 ?x ?tau } // -- | { AcceptTypeUnion ?c ?x ?tau } ;
! CHR: propagate-accept-union @ { CondJump ?c ?c1 } { ProvideTypeUnion ?c1 ?x ?tau } // -- | { ProvideTypeUnion ?c ?x ?tau } ;

! This reasoning is propagated to top-level ?
! CHR{ { Type ?x ?tau } // { Type ?x ?tau } -- | }
! CHR: type-conflict @ { Type ?x ?tau } { Type ?x ?sig } // -- [ ?tau ?sig = not ] | [ "double type spec" throw ] ;
! CHR: instance-type @ { Cond ?c P{ Instance ?x ?tau } } // -- | { Cond ?c P{ Type ?x ?tau } } ; ! { Subtype ?tau1 ?tau } { Subtype ?tau ?tau1 } ;
CHR: instance-type @ P{ Instance ?x ?tau } // -- | P{ Type ?x ?tau } ; ! { Subtype ?tau1 ?tau } { Subtype ?tau ?tau1 } ;
! CHR: accept-type @ { AcceptType ?c ?x ?tau } // -- | { Cond ?c { Type ?x ?tau1 } } { Subtype ?tau ?tau1 } ;
! CHR: provide-type @ { ProvideType ?c ?x ?tau } // -- | { Cond ?c { Type ?x ?tau1 } } { Subtype ?tau1 ?tau } ;
! CHR: { Subtype ?tau2 ?tau3 } // { Subtype ?tau }

! ** Phi stuff
CHR: trivial-union @ // { UnionType ?tau3 ?tau1 ?tau1 } -- | [ ?tau3 ?tau1 ==! ] ;

! NOTE: Here we bubble types upwards already during compilation!
! CHR: propagate-accept @ { CondJump ?r ?c1 } { CondJump ?r ?c2 } { AcceptType ?c1 ?x ?tau1 } { AcceptType ?c2 ?x ?tau2 } // -- |
! CHR: propagate-accept @ { Branch ?r ?c1 ?c2 } { AcceptType ?c1 ?x ?tau1 } { AcceptType ?c2 ?x ?tau2 } // -- |
!    { AcceptType ?r ?x ?tau3 } { UnionType ?tau3 ?tau1 ?tau2 } ;

! CHR: propagate-phi-in @ { Branch ?r ?c1 ?c2 } { Cond ?c1 P{ Same ?x ?a } } { Cond ?c2 P{ Same ?x ?b } } // -- |
! { Type ?x ?tau3 } { Type ?a ?tau1 } { Type ?b ?tau2 } { UnionType ?tau3 ?tau1 ?tau2 } ;
! CHR: propagate-phi-out @ { Branch ?r ?c1 ?c2 } { Cond ?c1 P{ Same ?a ?y } } { Cond ?c2 P{ Same ?b ?y } } // -- |
! { Type ?y ?tau3 } { Type ?a ?tau1 } { Type ?b ?tau2 } { UnionType ?tau3 ?tau1 ?tau2 } ;

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
