USING: accessors arrays chr.factor chr.parser chr.state classes classes.algebra
classes.builtin classes.singleton classes.tuple classes.tuple.private
combinators combinators.short-circuit continuations kernel kernel.private lists
macros.expander math quotations sequences sets sorting terms types.util words ;

IN: chr.factor.intra-effect


! * Simplification/Intra-Effect reasoning

CHRAT: chr-intra-effect { }

CHR: invalid-stays-invalid @ { Invalid } // { Invalid } -- | ;


! *** Normalizations
CHR: comm-var-is-lhs @ // AS: ?p <={ commutative-pred A{ ?l } ?v } -- [ ?v term-var? ] |
[ { ?v ?l } ?p class-of slots>tuple ] ;

CHR: literal-f-is-class-f @ // { Instance ?x W{ f } } -- | { Instance ?x POSTPONE: f } ;

CHR: literal-singleton-class-is-class @ // { Instance ?x ?tau } -- [ { ?tau } first wrapper? ] [ { ?tau } first wrapped>> :>> ?rho singleton-class? ] |
{ Instance ?x ?rho } ;

CHR: normalize-not-type @ // { NotInstance ?x A{ ?tau } } -- [ { ?tau } first classoid? ]
[ { ?tau } first class-not :>> ?sig ] |
{ Instance ?x ?sig } ;


! ! Flatten union classes for now.
! CHR: flatten-union-instance @ // { Instance ?x A{ ?tau } } -- [ { ?tau } first :>> ?rho union-class? ] |
! [| | ?rho flatten-class <anonymous-union> :> c
!  { Instance ?x c }
! ] ;

CHR: early-exit @ { Invalid } // <={ body-pred } -- | ;

! *** <Phi
! ! **** Discarding nested calls for recursion types
! CHR: clear-rec-type-rec-call @ { PhiMode } { FixpointMode } { PhiSchedule ?w __ __ } // { CallRecursive ?w __ __ } -- | ;

! CHR: invalid-union @ { Invalid } // { Keep __ } -- | ;

! **** Re-building identities
! NOTE: the only way how two of these can be present at the same time is if both effects specify
! the same bind after stack unification
! CHR: both-bind-same-var @ { PhiMode } // { Bind ?y ?x } { Bind ?y ?x } -- | [ ?y ?x ==! ] ;

! UNION: bound-propagated-preds Instance expr-pred ;
! CHR: propagate-bound-pred @ { PhiMode } { Bind ?y ?x } AS: ?p <={ bound-propagated-preds ?x . __ } // -- |
! [ ?p clone ?y >>val ] ;

! CHR: same-stays-valid @ { Phi ?z ?x } { Phi ?z ?y } // AS: ?p <={ val-pred ?x . ?xs } AS: ?q <={ val-pred ?y . ?xs } -- [ ?p ?q [ class-of ] same? ] |
! [ ?p clone ?z >>val ] ;
! **** Phi Parameter Handling

! NOTE: this is pretty tricky with regards to what constitutes valid criteria for /not/
! merging types during phi reasoning.  Couple of approaches:
! 1. Any joined type, be it input, internal, or output is considered to be in covariant position
! 2. Only output types are considered to be in covariant position
! 3. Some explicit dependency type magic determines under what conditions we want to be distinct...
! 4. Only keep separate cases if we have conflicting definitions of output row vars due to unknown effects

! Current approach: Something like 3, where the set of Params is defined
! explicitly, and contagious, by underlying conditionals

CHR: have-equivalence-deciders @ { PhiMode } { MakeEffect ?i ?o __ __ __ } // { Decider ?x } { Decider ?y }
-- [ ?x ?i list*>array in? ] [ ?y ?o list*>array in? ] | { Invalid } ;
CHR: have-input-decider @ { PhiMode } { MakeEffect ?i ?o __ __ __ } // { Decider ?x } { Discriminator ?y }
-- [ ?x ?i list*>array in? ] [ ?y ?o list*>array in? ] | { Invalid } ;
CHR: have-output-decider @ { PhiMode } { MakeEffect ?i ?o __ __ __ } // { Discriminator ?x } { Decider ?y }
-- [ ?x ?i list*>array in? ] [ ?y ?o list*>array in? ] | { Invalid } ;

CHR: phi-same-branch-pred @ { PhiMode } // AS: ?p <={ body-pred } AS: ?q <={ body-pred } -- [ ?p ?q == ] |
{ Keep ?p } ;

CHR: phi-disjoint-instance @ { PhiMode } { Instance ?x A{ ?rho } } { Instance ?x A{ ?tau } } // --
[ { ?rho ?tau } first2 classes-intersect? not ] | { Decider ?x } ;
CHR: phi-maybe-disjoint-instance @ { PhiMode } { Instance ?x A{ ?rho } } { Instance ?x A{ ?tau } } // --
[ { ?rho ?tau } first2 { [ classes-intersect? ] [ class= not ] } 2&& ] | { Discriminator ?x } ;
CHR: phi-union-instance @ { PhiMode } // { Instance ?x A{ ?rho } } { Instance ?x A{ ?tau } } --
[ { ?rho ?tau } first2 simplifying-class-or :>> ?sig ] | { Keep P{ Instance ?x ?sig } } ;

! TODO: check for isomorphic effects maybe?
! Higher order: If we find one effect or two different ones, this is unresolved control flow
CHR: phi-disjoint-effect-type @ { PhiMode } { Instance ?x ?e } // -- [ ?e valid-effect-type? ] |
{ Invalid } ;


CHR: phi-disjoint-le-lhs @ { PhiMode } { Le ?x ?v } { Lt ?v ?x } // -- [ ?x term-var? ] | { Discriminator ?x } ;
CHR: phi-disjoint-le-rhs @ { PhiMode } { Le ?v ?x } { Lt ?x ?v } // -- [ ?x term-var? ] | { Discriminator ?x } ;
! TODO: numerical predicates!

! ! ( x <= 5 ) ( 5 <= x ) -> union
! ! ( x <= 4 ) ( 5 <= x ) -> disjoint
! ! ( x <= 5 ) ( 4 <= x ) -> union
! CHR: phi-disjoint-output-range-le-le @ { PhiMode } // { Le ?x A{ ?m } } { Le A{ ?n } ?x } --
! [ ?m ?n < ] | { Invalid } ;
! ! ( x < 5 ) ( 5 <= x ) -> disjoint
! ! ( x < 4 ) ( 5 <= x ) -> disjoint
! ! ( x < 5 ) ( 4 <= x ) -> union
! CHR: phi-disjoint-output-range-lt-le @ { PhiMode } // { Lt ?x A{ ?m } } { Le A{ ?n } ?x } --
! [ ?m ?n <= ] | { Invalid } ;
! CHR: phi-disjoint-output-range-le-lt @ { PhiMode } // { Le ?x A{ ?m } } { Lt A{ ?n } ?x } --
! [ ?m ?n <= ] | { Invalid } ;
! ! ( x < 5 ) ( 5 < x ) -> disjoint
! ! ( x < 4 ) ( 5 < x ) -> disjoint
! ! ( x < 5 ) ( 4 < x ) -> union
! CHR: phi-disjoint-output-range-lt-lt @ { PhiMode } // { Le ?x A{ ?m } } { Lt A{ ?n } ?x } --
! [ ?m ?n <= ] | { Invalid } ;
! CHR: phi-disjoint-output-range-lt-eq @ { PhiMode } // { Eq ?x A{ ?n } } { Lt ?x A{ ?n } } -- | { Invalid } ;

! TODO: this is not recursive!
! NOTE: Rationale: An effect type is refined by its body predicates, which act as set subtraction.
! So the more general type is the one which has body predicates that both must agree on.
! If they have the same set of parameters but different bodies, they define a dependent type.
! CHR: phi-phiable-effect-instance @ { PhiMode } // { Instance ?x P{ Effect ?a ?b ?r ?k } } { Instance ?x P{ Effect ?c ?d ?s ?l } } --
! [ ?r empty? ] [ ?s empty? ]
! [ { ?a ?b } { ?c ?d } unify ] |
! [ { ?a ?b } { ?c ?d } ==! ]
! [| | ?l ?k intersect :> body
!  P{ Keep P{ Instance ?x P{ Effect ?a ?b f body } } }
! ] ;
! ! **** phi union types
! CHR: phi-instance @ { Phi ?z ?x } { Phi ?z ?y } // { Instance ?x A{ ?rho } } { Instance ?y A{ ?sig } } --
! [ { ?rho ?sig } first2 class-or :>> ?tau ] |
! { Instance ?z ?tau } ;

! Slots
! CHR: phi-slot @ { Phi ?z ?x } { Phi ?z ?y } // { Slot ?x ?n ?a } { Slot ?y ?n ?b } -- |
! { Phi ?c ?a } { Phi ?c ?b } { Slot ?z ?n ?c } ;

! **** Relational reasoning
! Transport relation in
! TODO: abstract to all relations somehow
! CHR: phi-eq @ { Phi ?a ?x } { Phi ?a ?y } { Phi ?b ?v } { Phi ?b ?w } // { Eq ?x ?y } { Eq ?v ?w } -- |
! { Eq ?a ?b } ;
! CHR: phi-neq @ { Phi ?a ?x } { Phi ?a ?y } { Phi ?b ?v } { Phi ?b ?w } // { Neq ?x ?y } { Neq ?v ?w } -- |
! { Neq ?a ?b } ;
! CHR: phi-eq-conflict @ { Phi ?a ?x } { Phi ?a ?y } { Phi ?b ?v } { Phi ?b ?w } // { Eq ?x ?y } { Neq ? }



! **** phi higher order

! If we have conflicting definitions on what will define an output stack, then we have unresolved control flow
! CHR: phi-call-effect-out-conflict @ { PhiMode } // { CallEffect ?p ?a ?x } { CallEffect ?q ?b ?x } -- [ ?p ?q == not ?a ?b == not or ] |
! { Invalid } ;


! CHR: phi-call-effect-match-in @ { Phi ?r ?p } { Phi ?r ?q }
! // { CallEffect ?p ?a ?b } { CallEffect ?q ?x ?y } -- |
! { PhiStack ?v ?a }
! { PhiStack ?v ?x }
! { PhiStack ?w ?b }
! { PhiStack ?w ?y }
! { CallEffect ?r ?v ?w } ;

! TODO: make this dependent on whether we simplify our own def!
! CHR: phi-call-rec-match @ { Phi ?r ?p } { Phi ?r ?q }
! // { CallRecursive ?w ?a ?b } { CallRecursive ?w ?x ?y } --
! { ?Phi ?v ?a ?x ?l }
! { ?Phi ?z ?b ?y ?l }
! |
! [ ?k Yes == ?l Yes == and
!   {
!       P{ PhiStack ?z ?a }
!       P{ PhiStack ?z ?x }
!       P{ CallRecursive ?w ?v ?z }
!   }
!   P{ Invalid } ?
! ] ;

! **** phi recursive calls

! We don't merge call-recursives for our own disjoint definition
CHR: phi-call-rec-self @ { PhiMode } { PhiSchedule ?w __ __ } //
{ CallRecursive ?w __ __ } -- | { Invalid } ;

! CHR: phi-call-rec-have-type @ { PhiMode } { FixpointTypeOf ?w ?e } // { CallRecursive ?w ?a ?b } -- [ ?e full-type? ] |
! [ { ?a ?b } { ?c ?d } ==! ]
! { Params ?x }
! [ ?l ] ;
! [| | ?e fresh-effect { [ in>> ] [ out>> ] [ parms>> ] [ preds>> ] } cleave
!  :> ( in out parms preds )
!  {
!      [ { ?a ?b } ]
!  }
! ]

! **** Conditions under which even a single pred can conserve disjunctivity
! CHR: disj-output-maybe-callable @ { PhiMode } { MakeEffect __ ?b __ __ __ } // { Instance ?x A{ ?tau } } --
! [ ?x ?b vars in? ] [ { ?tau } first classoid? ] [ { ?tau } first callable classes-intersect? ] | { Invalid } ;

! CHR: disj-param-maybe-callable @ { PhiMode } <={ MakeEffect } { Params ?l } // { Instance ?x A{ ?tau } } --
! [ ?x ?l in? ] [ { ?tau } first classoid? ] [ { ?tau } first callable classes-intersect? ] | { Invalid } ;

CHR: disj-is-macro-effect @ { PhiMode } <={ MakeEffect } // <={ MacroCall } -- | { Invalid } ;

! NOTE: this is pretty eager, as it will preserve all higher-order parametrism explicitly
CHR: disj-is-inline-effect @ { PhiMode } <={ MakeEffect } // <={ CallEffect ?p . __ } -- | { Invalid } ;

! Unknown call-rec
CHR: disj-single-call-rec @ { PhiMode } <={ MakeEffect } // <={ CallRecursive } -- | { Invalid } ;

! CHR: disj-single-effect @ { PhiMode } <={ MakeEffect } // { Instance ?x P{ Effect __ __ __ __ } } -- | { Invalid } ;

! TODO: does that reasoning work? Basically, we would need to have absence as failure here...
! CHR: disj-unknown-can-be-callable @ { PhiMode } <={ MakeEffect } // { Instance ?x A{ ?tau } }

CHR: disj-symbolic-type @ { PhiMode } <={ MakeEffect } { Params ?b } // { Instance ?x ?tau } -- [ ?tau term-var? ] [ ?x ?b in? ] | { Invalid } ;
CHR: disj-symbolic-compl-type @ { PhiMode } <={ MakeEffect } { Params ?b } // { NotInstance ?x ?tau } -- [ ?tau term-var? ] [ ?x ?b in? ] | { Invalid } ;

! *** Phi>

! TODO: extend to other body preds
CHR: unique-instance @ { Instance ?x ?tau } // { Instance ?x ?tau } -- | ;

CHR: uniqe-slot @ { Slot ?o ?n ?v } // { Slot ?o ?n ?v } -- | ;

CHR: merge-params @ // { Params ?x } { Params ?y } -- [ ?x ?y union >array :>> ?z ] | { Params ?z } ;

! NOTE: the reasoning is that this can inductively only happen during composition of two straight-line
! effects. So the instance in the first one is a "provide", and the instance in the second one is an "expect".
! Since the intersection type operation is commutative, we don't care which came from which.
CHR: same-slot-must-be-same-var @ { Slot ?o ?n ?v } // { Slot ?o ?n ?w } -- | [ ?v ?w ==! ] ;

: typeof>tag ( quoted -- n/f )
    first
    {
        { [ dup wrapper? ] [ wrapped>> tag ] }
        { [ dup tuple-class? ] [ drop tuple class>type ] }
        { [ dup class? ] [ class>type ] }
        [ drop f ]
    } cond ;

! *** Instance reasoning
CHR: check-tag @ { Instance ?x A{ ?v } } // { Tag ?x A{ ?n } } -- [ { ?v } typeof>tag :>> ?m ] |
[ ?m ?n = f { Invalid } ? ] ;

CHR: literal-defines-tag @ { Instance ?x A{ ?v } } { Tag ?x ?n } // -- [ { ?v } typeof>tag :>> ?m ]
[ ?v tag :>> ?m ] | { Instance ?n W{ ?m } } ;

CHR: convert-tag @ // { Tag ?x A{ ?n } } -- [ ?n type>class :>> ?tau ] |
{ Instance ?x ?tau } ;

CHR: instance-of-non-classoid @ { Instance ?x A{ ?c } } // -- [ { ?c } first classoid? not ] | { Invalid } ;

! CHR: useless-instance @ // { Instance __ object } -- | ;
CHR: null-instance-is-invalid @ { Instance ?x null } // -- | { Invalid } ;

! NOTE: this could be activated in phi mode if not careful
CHR: type-contradiction @ // { NotInstance ?x ?tau } { Instance ?x ?tau } -- | { Invalid } ;

! NOTE: There are two ways to handle intersections: in factor's type system in
! the intersection instance type, or in the
! implicit conjunction of the constraint store.  Currently, this is put into the
! intersection classes of the factor type system.
CHR: instance-intersection @
// { Instance ?x A{ ?tau } } { Instance ?x A{ ?sig } } --
[ { ?tau ?sig } first2 simplifying-class-and :>> ?c ] |
{ Instance ?x ?c } ;

CHR: instance-intersect-effect @ { Instance ?x ?e }
// { Instance ?x A{ ?tau } } --
[ ?e valid-effect-type? ] |
[ ?tau callable classes-intersect?
 f { Invalid } ? ] ;

! TODO: used? looks like should be subsumed by null-instance-is-invalid
CHR: call-null-instance-is-invalid @ { CallEffect ?x __ __ } { Instance ?x null } // -- | { Invalid } ;

! *** Macro Expansion/Folding
! NOTE: destructive
CHR: adjust-macro-stack @ // { MacroCall ?w f ?a ?b } -- [ ?w word? ] [ ?w "transform-n" word-prop :>> ?n ]
[ ?w "transform-quot" word-prop :>> ?q ] |
[| |
 ?n "v" utermvar <array> :> mparms
 mparms <reversed> >list ?rho lappend :> sin
 {
     [ ?a sin ==! ]
     { MacroCall ?q mparms sin ?b }
 }
] ;

! *** Arithmetics
! CHR: unique-expr-pred @ AS: ?p <={ expr-pred ?a . ?x } // AS: ?q <={ expr-pred ?a . ?x } -- [ ?p class-of ?q class-of class= ] | ;

CHR: check-le @ // { Le A{ ?x } A{ ?y } } -- [ ?x ?y <= not ] | { Invalid } ;
CHR: check-le-same @ // { Le ?x ?x } -- | ;
CHR: check-lt @ // { Lt A{ ?x } A{ ?y } } -- [ ?x ?y < not ] | { Invalid } ;
CHR: lt-tightens-le @ { Lt ?x ?y } // { Le ?x ?y } -- | ;
CHR: le-defines-eq @ // { Le ?x ?y } { Le ?y ?x } -- | { Eq ?x ?y } ;
CHR: lt-defines-neq @ // { Lt ?x ?y } { Lt ?y ?x } -- | { Neq ?x ?y } ;
! CHR: check-lt-1 @ // { Lt ?x ?y } { Lt ?y ?x } -- | { Invalid } ;
CHR: check-lt-same @ // { Lt ?x ?x } -- | { Invalid } ;
CHR: check-lt-eq-1 @ // { Lt ?x ?y } { Eq ?x ?y } -- | { Invalid } ;
CHR: check-lt-eq-2 @ // { Lt ?x ?y } { Eq ?y ?x } -- | { Invalid } ;
CHR: check-eq-1 @ // { Eq ?x ?y } { Neq ?x ?y } -- | { Invalid } ;
CHR: check-eq-2 @ // { Eq ?x ?y } { Neq ?y ?x } -- | { Invalid } ;
CHR: check-neq @ // { Neq A{ ?x } A{ ?y } } -- [ ?x ?y == ] | { Invalid } ;
! Being not equal to something we can't be anyway is redundant
CHR: redundant-neq @ { Instance ?x ?c } // { Neq ?x A{ ?l } } --
[ { ?l } first ?c instance? not ] | ;
CHR: redundant-neq-instance @ { Instance ?x A{ ?c } } { Instance ?y A{ ?d } } //
{ Neq ?x ?y } -- [ { ?c ?d } first2 classes-intersect? not ] | ;

CHR: check-sum @ // { Sum A{ ?z } A{ ?x } A{ ?y } } -- [ ?x ?y + ?z = not ] | P{ Invalid } ;
! CHR: zero-sum-1 @ // { Sum ?z 0 ?y } -- | [ ?z ?y ==! ] ;
! CHR: zero-sum-2 @ // { Sum ?z ?x 0 } -- | [ ?z ?x ==! ] ;
CHR: define-sum @ // { Sum ?z A{ ?x } A{ ?y } } --
[ ?x ?y + <wrapper> :>> ?v ] | { Instance ?z ?v } ;
CHR: normalize-sum @ // { Sum ?z A{ ?x } ?y } -- [ ?y term-var? ] | { Sum ?z ?y ?x } ;

CHR: check-prod @ // { Prod A{ ?z } A{ ?x } A{ ?y } } -- [ ?x ?y * ?z = not ] | P{ Invalid } ;
CHR: neutral-prod-1 @ // { Prod ?z 1 ?y } -- | [ ?z ?y ==! ] ;
CHR: neutral-prod-2 @ // { Prod ?z ?x 1 } -- | [ ?z ?x ==! ] ;
CHR: zero-prod-1 @ // { Prod ?z 0 ?y } -- | { Instance ?z 0 } ;
CHR: zero-prod-2 @ // { Prod ?z ?y 0 } -- | { Instance ?z 0 } ;
CHR: define-prod @ // { Prod ?z A{ ?x } A{ ?y } } --
[ ?x ?y * <wrapper> :>> ?v ] | { Instance ?z ?v } ;

CHR: check-shift @ // { Shift A{ ?z } A{ ?x } A{ ?n } } -- [ ?x ?n shift ?z = not ] | P{ Invalid } ;
CHR: neutral-shift @ // { Shift ?z ?x 0 } -- | [ ?z ?x ==! ] ;
CHR: zero-shift @ // { Shift ?z 0 ?x } -- | { Instance ?z W{ 0 } } ;
CHR: define-shift @ // { Shift ?z A{ ?x } A{ ?n } } --
[ ?x ?n shift <wrapper> :>> ?v ] | { Instance ?z ?v } ;

CHR: check-bitand @ // { BitAnd A{ ?z } A{ ?x } A{ ?y } } -- [ ?x ?y bitand ?z = not ] | { Invalid } ;
CHR: zero-bitand-1 @ // { BitAnd ?z 0 ?y } -- | { Instance ?z W{ 0 } } ;
CHR: zero-bitand-2 @ // { BitAnd ?z ?x 0 } -- | { Instance ?z W{ 0 } } ;
CHR: neutral-bitand-1 @ // { BitAnd ?z -1 ?y } -- | [ ?z ?y ==! ] ;
CHR: neutral-bitand-2 @ // { BitAnd ?z ?x -1 } -- | [ ?z ?x ==! ] ;

! CHR: propagate-lt-offset @ { Lt A{ ?n } ?x } { Sum ?z ?x A{ ?y } } // --
! [ ?n ?y + :>> ?m ] | { Lt ?m ?z } ;
! CHR: propagate-lt-offset @ { Lt ?n ?x } { Sum ?z ?x ?y } // -- |
! { Sum ?w ?n ?y } { Lt ?z ?w } ;

! *** Call Effect matching
! NOTE: These only meet in renamed form?
! CHR: call-applies-effect @ { Instance ?q P{ Effect ?c ?d ?x ?l } } { CallEffect ?q ?a ?b } // -- |
CHR: call-applies-effect @ { Instance ?q P{ Effect ?c ?d ?x ?l } } // { CallEffect ?q ?a ?b } -- |
[ { ?a ?b } { ?c ?d } ==! ]
{ Params ?x }
[ ?l ] ;

! NOTE: Idea: create an iteration constraint.  Should only be active in subsequent compositions
CHR: call-recursive-iteration @ { FixpointTypeOf ?w ?rho } // { CallRecursive ?w ?a ?b } --
[ ?rho full-type? ] |
[| |
 ?rho fresh-effect [ in>> ] [ out>> ] [ preds>> ] tri :> ( ilast olast plast )
 {
     [ ?b olast ==! ]
     P{ Iterated ?a ilast }
 } plast append
] ;


! NOTE: we don't apply the inputs here, so we should have the effect of a Kleene star for an unknown number of
! Iterations.  The predicates relating to the inputs of the union type should then be discarded.
! CHR: call-recursive-applies-fixpoint-effect @ { FixpointTypeOf ?w ?e } // { CallRecursive ?w ?a ?b } -- [ ?e full-type? ] |
! [| | ?e fresh-effect { [ in>> ] [ out>> ] [ parms>> ] [ preds>> ] } cleave
!  :> ( in out parms preds )
!  preds out ?b [ solve-eq lift ] no-var-restrictions
!  ! {
!  !     ! [ { ?a ?b } { in out } ==! ]
!  !     ! [ ?b out ==! ]
!  !     ! P{ Params parms }
!  ! }
!  ! preds append
! ] ;

! NOTE: explicitly instantiating dispatch effects for the three callables here

CHR: call-destructs-curry @ { Instance ?q curried } { Slot ?q "quot" ?p } { Slot ?q "obj" ?x } // { CallEffect ?q ?a ?b } -- |
{ CallEffect ?p L{ ?x . ?a } ?b } ;

CHR: call-destructs-composed @ { Instance ?p composed } { Slot ?p "first" ?q } { Slot ?p "second" ?r } // { CallEffect ?p ?a ?b } -- |
{ CallEffect ?q ?a ?rho } { CallEffect ?r ?rho ?b } ;

! *** Declarations

CHR: did-ensure @ // { Ensure +nil+ __ } -- | ;
CHR: did-declare @ // { Declare +nil+ __ } -- | ;
CHR: start-ensure @ // { Ensure A{ ?a } ?r } -- [ ?a array? ]
[ ?a <reversed> >list :>> ?b ] | { Ensure ?b ?r } ;
CHR: destruc-ensure @ // { Ensure L{ ?tau . ?r } L{ ?x . ?xs } } -- |
! { Ensure ?tau ?x }
{ Instance ?x ?tau }
{ Ensure ?r ?xs } ;
! NOTE: destructive!
CHR: ensure-stack @ { Ensure L{ ?tau . ?r } ?x } // -- [ ?x term-var? ] |
[ ?x L{ ?y . ?ys } ==! ] ;
! NOTE: destructive!
CHR: declare-ensures @ { Declare L{ ?tau . ?r } ?x } // -- |
{ Ensure L{ ?tau . ?r } ?x } ;
CHR: destruc-declare @ // { Declare L{ ?tau . ?r } L{ ?x . ?xs } } -- |
{ Params { ?x } }
{ Declare ?r ?xs } ;

! UNION: abstract-class union-class predicate-class ;
! CHR: apply-predicate-ensure @ { Ensure A{ ?tau } ?x } // -- [ ?x term-var? ] [ ?tau abstract-class? ] |
! { Instance ?x ?tau } ;
! CHR: apply-ensure @ // { Ensure A{ ?tau } ?x } -- [ ?x term-var? ] [ ?tau abstract-class? not ] |
! { Instance ?x ?tau } ;

! *** Substituting ground values into body constraints

CHR: known-declare @
! NOTE: for some reason, we can't match into W{ ?v } objects correctly...
{ Instance ?l A{ ?tau } } // { Declare ?l ?a } --
[ { ?tau } first wrapper? ]
[ ?tau <reversed> >list :>> ?m ] | { Declare ?m ?a } ;


CHR: known-macro-arg @ { Instance ?x A{ ?v } } // { MacroCall ?q ?a L{ ?x . ?ys } ?o } -- [ { ?v } first wrapper? ]
[ { ?v } first wrapped>> :>> ?z ]
[ ?a ?z prefix :>> ?b ]
|
{ MacroCall ?q ?b ?ys ?o } ;

! NOTE: only fully expanded macros are treated for now!
CHR: expand-macro @ // { MacroCall ?w ?a ?i ?o } -- [ ?a length ?w macro-effect = ]
[ ?w macro-quot :>> ?q ]
[ ?a ?q with-datastack first :>> ?p ]
|
{ CallEffect ?tau ?i ?o }
! NOTE: this should trigger only after the current constraint set is finished!
{ ?TypeOf ?p ?tau }
    ;

! CHR: constant-ensure @ // { Ensure ?l ?a } -- [ ?l array? ]
! [ ?l <reversed> >list :>> ?m ] |
! { Ensure ?m ?a } ;

CHR: known-slot @ { Instance ?n A{ ?tau } } // { Slot ?o ?n ?v } -- |
{ Slot ?o ?tau ?v } ;

CHR: known-instance @ { Instance ?c A{ ?tau } } // { Instance ?x ?c } --
[ { ?tau } first wrapper? ]
[ { ?tau } first wrapped>> :>> ?d drop t ] | { Instance ?x ?d } ;

CHR: known-not-instance @ { Instance ?c A{ ?tau } } // { NotInstance ?x ?c } --
[ { ?tau } first wrapper? ]
[ { ?tau } first wrapped>> :>> ?d drop t ] | { NotInstance ?x ?d } ;

CHR: known-tag-num @ { Instance ?n A{ ?v } } // { Tag ?c ?n } -- [ { ?v } first wrapper? ] [ ?v :>> ?w ] |
{ Tag ?c ?w } ;


! NOTE: this is still a bit tedious...Maybe we can have nice things? (Directly substitute literals...)
CHR: known-expr-val @ { Instance ?n ?v } // AS: ?p <={ expr-pred } -- [ ?n ?p vars in? ]
[ { ?v } first wrapper? ]
[ { ?v } first wrapped>> :>> ?w ]
|
[ ?p { { ?n ?w } } lift* ] ;

! *** Slot conversion
CHR: known-named-slot @ { Instance ?o A{ ?tau } } // { Slot ?o A{ ?n } ?v } -- [ ?tau tuple-class? ]
[ ?tau all-slots [ offset>> ?n = ] find nip :>> ?s ] [ ?s name>> :>> ?m ]
[ ?s class>> :>> ?rho ]
|
{ Slot ?o ?m ?v }
{ Instance ?v ?rho } ;

CHR: known-boa-spec @ { Instance ?c A{ ?v } } // AS: ?p <={ Boa ?c ?i ?o } -- |
[ ?p ?v >>spec ] ;

! *** Boa handling
! NOTE: This is a crucial point regarding re-definitions if we consider incremental operation
CHR: normalize-tuple-boa @ // { Boa A{ ?v } ?i ?o } --
[ ?v tuple-layout :>> ?c ] |
{ TupleBoa ?c ?i ?o } ;

! NOTE: Completely ignoring the hierarchy here
! NOTE: destructive
CHR: tuple-boa-decl @ // { TupleBoa A{ ?c } ?a ?b } --
[ ?c first :>> ?tau ] |
[| |
 ?tau name>> utermvar :> ov
 V{ } clone :> in-vars
 V{ } clone :> preds
 ?tau all-slots [ offset>> ] sort-with
 [| spec i |
     spec name>> :> n
     i n elt>var :> iv
     iv in-vars push
     P{ Slot ov n iv } preds push
     spec class>> :> c
     P{ Instance iv c } preds push
 ] each-index
 in-vars <reversed> >list ?rho lappend :> sin
 P{ Instance ov ?tau } preds push
 L{ ov . ?rho  } :> sout
 [ { ?a ?b } { sin sout } ==! ] preds push
 preds <reversed> >array
] ;

;
