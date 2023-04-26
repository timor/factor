USING: accessors arrays chr.factor chr.factor.util chr.parser chr.state classes
classes.algebra classes.builtin classes.predicate classes.singleton
classes.tuple classes.tuple.private combinators combinators.short-circuit
continuations kernel kernel.private lists macros.expander math math.order
quotations sequences sets sorting terms types.util ;

IN: chr.factor.intra-effect


! * Simplification/Intra-Effect reasoning

CHRAT: chr-intra-effect { }

CHR: invalid-stays-invalid @ { Invalid } // { Invalid } -- | ;


! *** Mode-agnostic Normalizations
CHR: comm-var-is-lhs @ // AS: ?p <={ commutative-pred A{ ?l } ?v } -- [ ?v term-var? ] |
[ { ?v ?l } ?p class-of slots>tuple ] ;

! Not ideal.  If we do that, we mix value and type levels.
! CHR: literal-f-is-class-f @ // { Instance ?x W{ f } } -- | { Instance ?x POSTPONE: f } ;
! Same here
! CHR: literal-singleton-class-is-class @ // { Instance ?x ?tau } -- [ { ?tau } first wrapper? ] [ { ?tau } first wrapped>> :>> ?rho singleton-class? ] |
! { Instance ?x ?rho } ;

CHR: wrapper-type-is-eq @ // { Instance ?x ?tau } -- [ { ?tau } first wrapper? ] [ { ?tau } first wrapped>> :>> ?v
                                                                                   class-of :>> ?rho drop t ]
|
{ Instance ?x ?rho }
{ Eq ?x ?v } ;

! This is used to instantiate the branches of the instance check quotations
GENERIC: make-instance-check ( class -- quot/f )
M: classoid make-instance-check drop f ;
! M: singleton-class make-instance-check '[ _ eq? ] ;
M: predicate-class make-instance-check make-pred-quot ;

CHR: declared-singleton-class @ // { DeclaredInstance ?x A{ ?tau } } -- [ ?tau singleton-class? ] |
{ Instance ?x ?tau }
{ Eq ?x ?tau } ;

CHR: declared-not-singleton-class @ // { DeclaredNotInstance ?x A{ ?tau } } -- [ ?tau singleton-class? ]
[ ?tau class-not :>> ?rho ] |
{ Instance ?x ?rho }
{ Neq ?x ?tau } ;


CHR: declared-predicate-class @ // { DeclaredInstance ?x A{ ?tau } } -- [ ?tau predicate-class? ]
[ ?tau superclass-of :>> ?rho ]
[ ?tau make-instance-check :>> ?q ]
|
{ ?DeferTypeOf ?q ?sig }
{ Instance ?p ?sig }
{ CallEffect ?p L{ ?x . ?b } L{ ?c . ?b } }
{ Instance ?c W{ t } }
{ DeclaredInstance ?x ?rho } ;

CHR: declared-not-predicate-class @ // { DeclaredNotInstance ?x A{ ?tau } } -- [ ?tau predicate-class? ]
[ ?tau class-not :>> ?rho ]
[ ?tau make-instance-check :>> ?q ]
|
{ Instance ?x ?rho }
{ ?DeferTypeOf ?q ?sig }
{ Instance ?p ?sig }
{ CallEffect ?p L{ ?x . ?b } L{ ?c . ?b } }
{ Instance ?c W{ f } } ;

CHR: normalize-known-not-declaration @ // { DeclaredNotInstance ?x A{ ?tau } } -- [ { ?tau } first classoid? ]
[ { ?tau } first class-not :>> ?sig ] |
{ DeclaredInstance ?x ?sig } ;

CHR: declaration-is-assertion @ // { DeclaredInstance ?x A{ ?tau } } -- |
{ Instance ?x ?tau } ;


! ! Flatten union classes for now.
! CHR: flatten-union-instance @ // { Instance ?x A{ ?tau } } -- [ { ?tau } first :>> ?rho union-class? ] |
! [| | ?rho flatten-class <anonymous-union> :> c
!  { Instance ?x c }
! ] ;

CHR: early-exit @ { Invalid } // <={ body-pred } -- | ;

! *** <Phi
PREFIX-RULES: P{ PhiMode }

CHR: no-deferred-inference-in-phi-mode @ // <={ ?DeferTypeOf } -- |
[ "deferred inference in phi mode" throw ] ;

! ! **** Discarding nested calls for recursion types
! CHR: clear-rec-type-rec-call @ { FixpointMode } { PhiSchedule ?w __ __ } // { CallRecursive ?w __ __ } -- | ;

! CHR: invalid-union @ { Invalid } // { Keep __ } -- | ;

! **** Phi Parameter Handling

! NOTE: this is pretty tricky with regards to what constitutes valid criteria for /not/
! merging types during phi reasoning.  Couple of approaches:
! 1. Any joined type, be it input, internal, or output is considered to be in covariant position
! 2. Only output types are considered to be in covariant position
! 3. Some explicit dependency type magic determines under what conditions we want to be distinct...
! 4. Only keep separate cases if we have conflicting definitions of output row vars due to unknown effects

! Current approach: Something like 3, where the set of Params is defined
! explicitly, and contagious, by underlying conditionals

CHR: remove-empty-params @ // { Params ?l } { Params __ } -- [ ?l empty? ] | ;

CHR: keep-params-disjoint @ // { Params ?l } { Params ?k } -- [ ?l ?k intersect dup null? [ drop f ] when :>> ?d ]
[ ?l ?d diff :>> ?x drop t ]
[ ?k ?d diff :>> ?y drop t ]
| { Params ?x } { Params ?y } ;

! TODO prove that this does not work and discard
! If we encounter predicates that differ in vars which are locals, then try to unify them
! NOTE: this has the potential to create problems if we try to match predicates which have no ties to input or output
! vars and where multiple ones are present, because then we just guess which parameter corresponds to which without
! searching all possiblilities.  This could probably only be solved by CHR-OR...
! Ideally this can't happen, as the regular predicate collection mechanism via live-vars/defines-vars should
! ensure that at least some connection to input/output is carried through matching...
! CHR: merge-phi-params @ AS: ?p <={ body-pred } AS: ?q <={ body-pred } { Params ?l } { Params ?k } // --
! [ ?p ?q [ class-of ] same? ]
! [ ?p vars ?l intersects? ]
! [ ?q vars ?k intersects? ]
! ! TODO: get the right param membership check here lhs/rhs-wise!!!
! [
!     ! { ?p ?q ?l ?k } break f lift [ ?p ?q
!     !           ! [ solve-eq ] no-var-restrictions
!     !           ! f [ unify ] with-term-vars
!     !           unify
!     !           [ { [ drop ?l in? ] [ nip ?k in? ] } 2&& ] assoc-filter
!     !         ] with-term-vars
!     ?p ?q unify
!   [ f ]
!   [ >alist ] if-assoc-empty
!   :>> ?s  ] |
! [ ?s unzip ==! ] ;

CHR: already-decider @ { Decider ?x } // <={ Discriminator ?x } -- | ;
CHR: already-discriminator @ { Discriminator ?x } // { Discriminator ?x } -- | ;

CHR: destruc-decider @ // { Decider ?x } -- [ ?x sequence? ] |
[ ?x [ term-var? ] filter [ Decider boa ] map ] ;

CHR: destruc-discriminator @ // { Discriminator ?x } -- [ ?x sequence? ] |
[ ?x [ term-var? ] filter [ Discriminator boa ] map ] ;

! *** Deciding to declare disjoint

! NOTE: for now changing this to accept also a discriminator and at least one decider in the input...
! TODO: maybe rename { Invalid } to { Disjoint } in the Phi context...
! CHR: have-equivalence-deciders @ { MakeEffect ?i ?o __ __ __ } // { Decider ?x } { Decider ?y }
! -- [ ?x ?i list*>array in? ] [ ?y ?o list*>array in? ] | { Invalid } ;

! CHR: have-output-input-decider @ { MakeEffect ?i ?o __ __ __ } // { Decider ?x } { Discriminator ?y }
! -- [ ?x ?i list*>array in? ] [ ?y ?o list*>array in? ] | { Invalid } ;

! CHR: have-input-output-decider @ { MakeEffect ?i ?o __ __ __ } // { Discriminator ?x } { Decider ?y }
! -- [ ?x ?i list*>array in? ] [ ?y ?o list*>array in? ] | { Invalid } ;

! NOTE: This would also be one point where we could hold on to internal vars, but that is probably
! too sensitive?  If so, they would show up in the Params predicates
CHR: have-interesting-decider @ { MakeEffect ?i ?o __ __ __ } // <={ Discriminator ?x } { Decider ?y }
-- [ ?i ?o [ list*>array ] bi@ append [ ?x swap in? ] [ ?y swap in? ] bi and ] | { Invalid } ;

! *** Phi Predicate Handling

! NOTE: this takes this out of the reasoning.  However, anything that should be able to be reasoned
! from the existence of same information different branches should have done during composition already.
! After this rule, existence of predicates is assumed to be only present in one branch.
CHR: phi-same-branch-pred @ // AS: ?p <={ body-pred } AS: ?q <={ body-pred } -- [ ?p ?q == ] | { Keep ?p } ;

CHR: phi-disjoint-instance @ { Instance ?x A{ ?rho } } { Instance ?x A{ ?tau } } // --
[ { ?rho ?tau } first2 classes-intersect? not ] | { Decider ?x } ;

CHR: phi-maybe-disjoint-instance @ { Instance ?x A{ ?rho } } { Instance ?x A{ ?tau } } // --
[ { ?rho ?tau } first2 { [ classes-intersect? ] [ class= not ] } 2&& ] | { Discriminator ?x } ;

CHR: phi-union-instance @ // { Instance ?x A{ ?rho } } { Instance ?x A{ ?tau } } --
[ { ?rho ?tau } first2 simplifying-class-or :>> ?sig ] | { Keep P{ Instance ?x ?sig } } ;

! TODO: check for isomorphic effects maybe?
!  -> If so, this would have to be done in phi-same-branch-pred above...
! Higher order: If we find one effect or two different ones, this is unresolved control flow
CHR: phi-disjoint-effect-type @ { Instance ?x ?e } // -- [ ?e valid-effect-type? ] |
{ Invalid } ;


! ! ( x <= 5 ) ( 5 <= x ) -> union
! ! ( x <= 4 ) ( 5 <= x ) -> disjoint
! ! ( x <= 5 ) ( 4 <= x ) -> union
! CHR: phi-disjoint-output-range-le-le @ // { Le ?x A{ ?m } } { Le A{ ?n } ?x } --
! [ ?m ?n < ] | { Invalid } ;
! ! ( x < 5 ) ( 5 <= x ) -> disjoint
! ! ( x < 4 ) ( 5 <= x ) -> disjoint
! ! ( x < 5 ) ( 4 <= x ) -> union
! CHR: phi-disjoint-output-range-lt-le @ // { Lt ?x A{ ?m } } { Le A{ ?n } ?x } --
! [ ?m ?n <= ] | { Invalid } ;
! CHR: phi-disjoint-output-range-le-lt @ // { Le ?x A{ ?m } } { Lt A{ ?n } ?x } --
! [ ?m ?n <= ] | { Invalid } ;
! ! ( x < 5 ) ( 5 < x ) -> disjoint
! ! ( x < 4 ) ( 5 < x ) -> disjoint
! ! ( x < 5 ) ( 4 < x ) -> union
! CHR: phi-disjoint-output-range-lt-lt @ // { Le ?x A{ ?m } } { Lt A{ ?n } ?x } --
! [ ?m ?n <= ] | { Invalid } ;
! CHR: phi-disjoint-output-range-lt-eq @ // { Eq ?x A{ ?n } } { Lt ?x A{ ?n } } -- | { Invalid } ;

! TODO: this is not recursive!
! NOTE: Rationale: An effect type is refined by its body predicates, which act as set subtraction.
! So the more general type is the one which has body predicates that both must agree on.
! If they have the same set of parameters but different bodies, they define a dependent type.
! CHR: phi-phiable-effect-instance @ // { Instance ?x P{ Effect ?a ?b ?r ?k } } { Instance ?x P{ Effect ?c ?d ?s ?l } } --
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

CHR: phi-eq-decider @ { Eq ?x A{ ?b } } { Eq ?x A{ ?c } } // -- [ ?b ?c = not ] |
{ Decider ?x } ;
: order? ( obj1 obj2 -- min max ? )
    [ 2dup <=> +gt+ eq? [ swap ] when t ] [ drop f ] recover ;
CHR: phi-eq-range @ // { Eq ?x A{ ?b } } { Eq ?x A{ ?c } } -- [ ?b ?c order? [ :>> ?n drop :>> ?m drop ] dip ]
|
{ Keep P{ Le ?m ?x } }
{ Keep P{ Le ?n ?x } } ;
! TODO: abstract to all relations somehow

! NOTE: replacing these with discriminators for now.  The idea is that this is not an observable single-value
! difference thing in the input or output?
! CHR: phi-eq-neq-1 @ { Eq ?x ?y } { Neq ?x ?y } // -- | { Decider { ?x ?y } } ;
! CHR: phi-eq-neq-2 @ { Eq ?x ?y } { Neq ?y ?x } // -- | { Decider { ?x ?y } } ;
CHR: phi-eq-neq-1 @ { Eq ?x ?y } { Neq ?x ?y } // -- | { Discriminator { ?x ?y } } ;
CHR: phi-eq-neq-2 @ { Eq ?x ?y } { Neq ?y ?x } // -- | { Discriminator { ?x ?y } } ;
! CHR: phi-neq-is-always-decider @ { Neq ?x ?y } // -- | { Decider { ?x ?y } } ;

! CHR: phi-eq-lt-decider-1 @ // { Eq ?x ?y } { Lt ?x ?y } -- | { Decider { ?x ?y } } { Keep P{ Le ?x ?y } } ;
! CHR: phi-eq-lt-decider-2 @ // { Eq ?x ?y } { Lt ?y ?x } -- | { Decider { ?x ?y } } { Keep P{ Le ?y ?x } } ;
CHR: phi-eq-lt-decider-1 @ // { Eq ?x ?y } { Lt ?x ?y } -- | { Discriminator { ?x ?y } } { Keep P{ Le ?x ?y } } ;
CHR: phi-eq-lt-decider-2 @ // { Eq ?x ?y } { Lt ?y ?x } -- | { Discriminator { ?x ?y } } { Keep P{ Le ?y ?x } } ;

CHR: phi-eq-le-discrim-1 @ // { Eq ?x ?y } { Le ?x ?y } -- | { Discriminator { ?x ?y } } { Keep P{ Le ?x ?y } } ;
CHR: phi-eq-le-discrim-2 @ // { Eq ?y ?x } { Le ?x ?y } -- | { Discriminator { ?x ?y } } { Keep P{ Le ?x ?y } } ;

! CHR: phi-lt-lt-decider @ // { Lt ?x ?y } { Lt ?y ?x } -- | { Decider { ?y ?x } } ;
CHR: phi-lt-lt-decider @ // { Lt ?x ?y } { Lt ?y ?x } -- | { Discriminator { ?y ?x } } ;

! These are overlapping, so no deciders
CHR: phi-discrim-le-lt @ { Le ?x ?v } { Lt ?v ?x } // -- | { Discriminator { ?x ?v } } ;
! CHR: phi-discrim-le-rhs @ { Le ?v ?x } { Lt ?x ?v } // -- [ ?x term-var? ] | { Discriminator ?x } ;

! *** Phi-Mode single-branch predicates

! These are basically non-surviving single-branch variants
! The idea is that they do specify an aspect which only a part of the values of
! the other side would satisfy
CHR: phi-rel-discriminates @ <={ rel-pred ?x ?y } // -- | { Discriminator { ?x ?y } } ;

! **** phi higher order

! If we have conflicting definitions on what will define an output stack, then we have unresolved control flow
! CHR: phi-call-effect-out-conflict @ // { CallEffect ?p ?a ?x } { CallEffect ?q ?b ?x } -- [ ?p ?q == not ?a ?b == not or ] |
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
CHR: phi-call-rec-self @ { PhiSchedule ?w __ __ } //
{ CallRecursive ?w __ __ } -- | { Invalid } ;

! **** Conditions under which even a single pred can conserve disjunctivity
! CHR: disj-output-maybe-callable @ { MakeEffect __ ?b __ __ __ } // { Instance ?x A{ ?tau } } --
! [ ?x ?b vars in? ] [ { ?tau } first classoid? ] [ { ?tau } first callable classes-intersect? ] | { Invalid } ;

! CHR: disj-param-maybe-callable @ <={ MakeEffect } { Params ?l } // { Instance ?x A{ ?tau } } --
! [ ?x ?l in? ] [ { ?tau } first classoid? ] [ { ?tau } first callable classes-intersect? ] | { Invalid } ;

! TODO: need?
CHR: disj-is-macro-effect @ <={ MakeEffect } // { MacroExpand __ __ __ __ } -- | { Invalid } ;

! NOTE: this is pretty eager, as it will preserve all higher-order parametrism explicitly
CHR: disj-is-inline-effect @ <={ MakeEffect } // <={ CallEffect ?p . __ } -- | { Invalid } ;

! Unknown call-rec
CHR: disj-single-call-rec @ <={ MakeEffect } // <={ CallRecursive } -- | { Invalid } ;
! CHR: disj-single-call-rec @ // <={ CallRecursive } -- | { Invalid } ;

! That's a loop, don't merge

! CHR: disj-single-effect @ <={ MakeEffect } // { Instance ?x P{ Effect __ __ __ __ } } -- | { Invalid } ;

! TODO: does that reasoning work? Basically, we would need to have absence as failure here...
! CHR: disj-unknown-can-be-callable @ <={ MakeEffect } // { Instance ?x A{ ?tau } }

! Used in instance? case
CHR: disj-symbolic-type @ AS: ?e <={ MakeEffect } // { DeclaredInstance ?x ?tau } -- [ ?tau term-var? ] [ ?x ?e make-effect-vars in? ] | { Invalid } ;
CHR: disj-symbolic-compl-type @ AS: ?e <={ MakeEffect } // { DeclaredNotInstance ?x ?tau } -- [ ?tau term-var? ] [ ?x ?e make-effect-vars in? ] | { Invalid } ;

! *** Phi>

PREFIX-RULES: P{ CompMode }
! TODO: extend to other body preds
! Possibly expensive
! CHR: unique-body-pred @ AS: ?p <={ body-pred } // AS ?q <={ body-pred } -- [ ?p ?q = ] | ;
CHR: unique-instance @ { Instance ?x ?tau } // { Instance ?x ?tau } -- | ;

CHR: uniqe-slot @ { Slot ?o ?n ?v } // { Slot ?o ?n ?v } -- | ;

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
! Tags are an implementation detail, and are re-converted to classes as soon as possible
CHR: check-tag @ { Instance ?x A{ ?v } } // { Tag ?x A{ ?n } } -- [ { ?v } typeof>tag :>> ?m ] |
[ ?m ?n = f { Invalid } ? ] ;

CHR: literal-defines-tag @ { Instance ?x A{ ?v } } { Tag ?x ?n } // -- [ { ?v } typeof>tag :>> ?m ]
[ ?v tag :>> ?m ] | { Instance ?n W{ ?m } } ;

CHR: convert-tag @ // { Tag ?x A{ ?n } } -- [ ?n type>class :>> ?tau ] |
{ Instance ?x ?tau } ;

CHR: instance-of-non-classoid @ { Instance ?x A{ ?c } } // -- [ { ?c } first classoid? not ] | { Invalid } ;

CHR: null-instance-is-invalid @ // { Instance ?x null } -- | { Invalid } ;

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

! *** Arithmetics
CHR: unique-expr-pred @ AS: ?p <={ expr-pred ?a . ?x } // AS: ?q <={ expr-pred ?a . ?x } -- [ ?p class-of ?q class-of class= ] | ;

CHR: check-le @ // { Le A{ ?x } A{ ?y } } -- [ ?x ?y <= not ] | { Invalid } ;
CHR: check-le-same @ // { Le ?x ?x } -- | ;
CHR: check-lt @ // { Lt A{ ?x } A{ ?y } } -- [ ?x ?y < not ] | { Invalid } ;
CHR: lt-tightens-le @ { Lt ?x ?y } // { Le ?x ?y } -- | ;
CHR: lt-subsumes-lt-lhs @ <={ lt-pred ?x A{ ?m } } // <={ lt-pred ?x A{ ?n } } -- [ ?m ?n < ] | ;
CHR: lt-subsumes-lt-rhs @ <={ lt-pred A{ ?m } ?x } // <={ lt-pred A{ ?n } ?x } -- [ ?m ?n > ] | ;
CHR: reflexive-le-defines-eq @ // { Le ?x ?y } { Le ?y ?x } -- | { Eq ?x ?y } ;
CHR: reflexive-lt-defines-neq @ // { Lt ?x ?y } { Lt ?y ?x } -- | { Neq ?x ?y } ;
CHR: eq-tightens-le-1 @ { Eq ?x ?y } // { Le ?x ?y } -- | ;
CHR: eq-tightens-le-2 @ { Eq ?x ?y } // { Le ?y ?x } -- | ;
CHR: neq-tightens-le-1 @ // { Neq ?x ?y } { Le ?x ?y } -- | { Lt ?x ?y } ;
CHR: neq-tightens-le-2 @ // { Neq ?y ?x } { Le ?x ?y } -- | { Lt ?x ?y } ;
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
CHR: define-diff-1 @ // { Sum A{ ?z } ?x A{ ?y } } --
[ ?z ?y - <wrapper> :>> ?v ] | { Instance ?x ?v } ;
CHR: normalize-sum @ // { Sum ?z A{ ?x } ?y } -- [ ?y term-var? ] | { Sum ?z ?y ?x } ;
! Anything more complex than that needs a linear equation predicate...
CHR: transitive-literal-sum @ // { Sum ?z ?x A{ ?m } } { Sum ?x ?a A{ ?n } } --
[ ?m ?n + :>> ?k ]
| { Sum ?z ?a ?k } ;

! NOTE: this does not work transitively in a correct way
! TODO: may be better to do this with a linear combination predicate instead?
UNION: binary-expr Sum Prod ;
CHR: keep-intermediate-sum-1 @ <={ binary-expr ?z ?x ?y } <={ binary-expr ?x ?a ?b } // -- [ ?x term-var? ] | { ImpliesParam { ?z ?y ?a ?b } { ?x } } ;
CHR: keep-intermediate-sum-2 @ <={ binary-expr ?z ?y ?x } <={ binary-expr ?x ?a ?b } // -- [ ?x term-var? ] | { ImpliesParam { ?z ?y ?a ?b } { ?x } } ;

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
! Probably not. [ ... ] [ call ] keep looks fishy...
! NOTE: big change: make a fresh effect before every call
! TODO: since we do that here, remove a lot of other fresh-effects....
CHR: call-applies-effect @ { Instance ?q ?x } // { CallEffect ?q ?a ?b } -- [ ?x Effect? ]
[ ?x fresh-effect :>> ?e ]
[ ?e in>> :>> ?c drop
  ?e out>> :>> ?d drop
  ?e preds>> :>> ?l drop
  t ]
|
[ { ?a ?b }
  { ?c ?d } ==! ]
[ ?l ] ;

! non-copying
! CHR: call-applies-effect @ { Instance ?q P{ Effect ?c ?d ?x ?l } } // { CallEffect ?q ?a ?b } -- |
! [ { ?a ?b } { ?c ?d } ==! ]
! [ ?l ] ;

! Trying to apply a conditional is tricky.  The whole idea was to avoid this in the first place by always
! distributing effect composition through Xor types.  However, if we allow delayed expansion for macros,
! these (e.g. cond) expand to an Xor Type.  The same will probably be the case in non-trivial versions of
! delayed instance checks.  If we want to continue being able to arbitrarily compose word types independently of
! any specific word order, this must be admitted.
! Approach: Set up a continuation, which will cause the MakeEffect to be able to return an XOR.  For this,
! we need to capture the Effect inference state, and diverge into the respective Branches of the applied Xor effect
! type.  This needs to be done recursively if necessary.
! NOTE: we need to destructure this though for matching...
CHR: call-applies-xor-effect @ { Instance ?q P{ Xor ?c ?d } } // { CallEffect ?q ?a ?b } -- |
{ CallXorEffect P{ Xor ?c ?d } ?a ?b } ;

! *** TODO Recursive Iteration expansion
! P{ CallRecursive tag ?a ?b } holds the enter-in stack in ?a
! iterated approach:
! tag -prelude-> ?a -RecursionTypePre-> ?b =same-layout-as= ?c -RecursionTypePost-> -FixPointCondition-> ?d
! NOTE: current layout: initial var_n, var_1, var_0
! It may be necessary to change this to var_n , var_n-m , var_n-m-1 , var_0
CHR: break-recursive-iteration @ { Iterated ?w { ?a ?b ?c ?d } } // { CallRecursive ?w ?i ?o } --
|
[ ?c ?i ==! ] ;

! NOTE: Idea: create an iteration constraint.  Should only be active in subsequent compositions
CHR: call-recursive-iteration @ { FixpointTypeOf ?w ?rho } { RecursionTypeOf ?w ?sig } //
{ CallRecursive ?w ?i ?o } --
[ ?rho full-type? ]
[ ?sig full-type? ]
[ ?i fresh :>> ?c ]
[ ?i fresh :>> ?d ] |
{ Iterated ?w { ?i ?c ?d ?e } }
! Return Type call
{ Instance ?q ?rho }
{ CallEffect ?q ?e ?o }
! Iteration Type call, don't match output
{ Instance ?p ?sig }
{ CallEffect ?p ?c ?x }
{ LoopVar { ?i ?c ?d ?e } }
    ;

! *** Loop relation reasoning
CHR: already-loop-var @ { LoopVar ?x } // { LoopVar ?x } -- | ;

! NOTE: it might make sense to throw these away and regenerate them during next composition?
CHR: destruc-loop-var @ // { LoopVar { L{ ?w . ?ws } L{ ?x . ?xs } L{ ?y . ?ys } L{ ?z . ?zs } } } -- |
{ LoopVar { ?w ?x ?y ?z } }
{ LoopVar { ?ws ?xs ?ys ?zs } } ;

! This does not change from one iteration to another, so it can never change
CHR: loop-invariant @ // { LoopVar { ?w ?y ?y ?z } } --
! [ ?y term-var? ]
|
[ ?w ?y ==! ]
[ ?z ?y ==! ] ;

! TODO not 100% sure this is always correct?
CHR: loop-invariant-instance @ { LoopVar { ?w ?x ?y ?z } }
{ Instance ?x ?rho } { Instance ?y ?rho } // -- |
{ Instance ?w ?rho }
{ Instance ?z ?rho } ;

! TODO: this is even more questionable, but the idea is that we have a monotone relation between
! Input and output, and we exactly know that we only take the exact same branch, then the monotonicity
! can be extended backwards (and forwards, for that matter? )
CHR: loop-instance-specialize-backwards @ { LoopVar { ?w ?x ?y ?z } }
{ Instance ?x A{ ?rho } } { Instance ?y A{ ?sig } } // -- [ ?rho ?sig class< ] |
{ Instance ?w ?rho } ;

! If we know the iteration-by-iteration effect, we know how deep the loop
! digs into the stack during iteration, which we can use to adjust the output stack before
! the outro, as well as the input stack before the first iteration
! NOTE: doing this on LoopVar instead of Iterated, because that is not triggered
CHR: iteration-adjust-output-stack @ // { LoopVar { ?w ?x ?y ?z } } --
[ ?y ?z [ llength* ] bi@ > ]
[ ?x ?y known-compatible-stacks? ]
[ ?y fresh :>> ?b ] |
[ ?y ?b [ lastcdr ] bi@ ==! ]
[ ?z ?b ==! ]
{ LoopVar { ?w ?x ?y ?z } } ;

CHR: iteration-adjust-input-stack @ // { LoopVar { ?w ?x ?y ?z } } --
[ ?w ?x [ llength* ] bi@ < ]
[ ?x ?y known-compatible-stacks? ]
[ ?x fresh :>> ?a ] |
[ ?x ?a [ lastcdr ] bi@ ==! ]
[ ?w ?a ==! ]
{ LoopVar { ?w ?x ?y ?z } } ;

! TODO: once there is loc annotation, maybe return useful syntax error?
CHR: invalid-loop-effect @ // { LoopVar { ?w ?x ?y ?z } } --
[ ?x ?y [ llength* ] same? not ]
[ ?x ?y [ lastcdr ] same? ] | { Invalid } ;

! **** Find Loop Counters
! TODO: Test if sum is always normalized for this?
! Define Counters.  Note that These define _inclusive_ intervals, because
! If the sum is assumed to have been calculated, then the result is included
CHR: loop-sum-defines-counters @ { Sum ?y ?x ?n } // { LoopVar { ?w ?x ?y ?z } } -- |
! CHR: loop-sum-defines-counters @ { Sum ?y ?x ?n } { LoopVar { ?w ?x ?y ?z } } // -- |
! pre-loop-body
{ Counter ?x ?w ?a ?n }
{ Sum ?z ?a ?n }
! post-loop-body
{ Counter ?y ?b ?z ?n }
{ Sum ?b ?w ?n }
;

! TODO cases for lt?
! If we now we are descending by constant amount m,
! then the final value can only be in m-range of a lower loop bound (Assuming we terminate!)
CHR: tighten-loop-bound-desc @ { Counter ?x ?a ?b A{ ?m } } { Le ?b A{ ?n } } // --
[ ?m 0 < ]
[ ?m 1 + ?n + :>> ?k ]
| { Le ?k ?b } ;
CHR: tighten-loop-bound-asc @ { Counter ?x ?a ?b A{ ?m } } { Le A{ ?n } ?b } // --
[ ?m 0 > ]
[ ?m 1 - ?n + :>> ?k ]
| { Le ?b ?k } ;

! TODO: implement based on predicates on the step, too?
! CHR: known-down-counter-literal @ // { Counter ?x ?a ?b A{ ?n } } -- [ ?n 0 < ] |
CHR: known-down-counter-literal @ { Counter ?x ?a ?b A{ ?n } } // -- [ ?n 0 < ] |
{ Le ?x ?a }
{ Le ?b ?x } ;


! *** TODO Modular arithmetic
! Needed for fixed-width computations, possibly some loop analysis/transformation foo


! *** Calling Curry/Compose

CHR: call-destructs-curry @ { Instance ?q curried } { Slot ?q "quot" ?p } { Slot ?q "obj" ?x } // { CallEffect ?q ?a ?b } -- |
{ CallEffect ?p L{ ?x . ?a } ?b } ;

CHR: call-destructs-composed @ { Instance ?p composed } { Slot ?p "first" ?q } { Slot ?p "second" ?r } // { CallEffect ?p ?a ?b } -- |
{ CallEffect ?q ?a ?rho } { CallEffect ?r ?rho ?b } ;

! *** Declarations
! TODO: why are there Ensure and Declare?

CHR: did-ensure @ // { Ensure +nil+ __ } -- | ;
CHR: did-declare @ // { Declare +nil+ __ } -- | ;
CHR: start-ensure @ // { Ensure A{ ?a } ?r } -- [ ?a array? ]
[ ?a <reversed> >list :>> ?b ] | { Ensure ?b ?r } ;
CHR: destruc-ensure @ // { Ensure L{ ?tau . ?r } L{ ?x . ?xs } } -- |
! { Ensure ?tau ?x }
{ DeclaredInstance ?x ?tau }
{ Ensure ?r ?xs } ;
! NOTE: destructive!
CHR: ensure-stack @ { Ensure L{ ?tau . ?r } ?x } // -- [ ?x term-var? ] |
[ ?x L{ ?y . ?ys } ==! ] ;
! NOTE: destructive!
CHR: declare-ensures @ { Declare L{ ?tau . ?r } ?x } // -- |
{ Ensure L{ ?tau . ?r } ?x } ;
CHR: destruc-declare @ // { Declare L{ ?tau . ?r } L{ ?x . ?xs } } -- |
{ Declare ?r ?xs } ;

! UNION: abstract-class union-class predicate-class ;
! CHR: apply-predicate-ensure @ { Ensure A{ ?tau } ?x } // -- [ ?x term-var? ] [ ?tau abstract-class? ] |
! { Instance ?x ?tau } ;
! CHR: apply-ensure @ // { Ensure A{ ?tau } ?x } -- [ ?x term-var? ] [ ?tau abstract-class? not ] |
! { Instance ?x ?tau } ;

! *** Substituting ground values into body constraints

CHR: known-declare @
{ Eq ?l A{ ?tau } } // { Declare ?l ?a } --
[ ?tau <reversed> >list :>> ?m ] | { Declare ?m ?a } ;


! **** Macro Expansion/Folding

CHR: known-macro-quot @ // { MacroExpand ?w ?a ?i ?x } -- [ ?w macro-quot :>> ?q ]
[ ?w macro-effect :>> ?n ] |
{ ExpandQuot ?q ?a ?i ?x ?n } ;

CHR: known-macro-arg @ { Eq ?x A{ ?v } } // { ExpandQuot ?q ?a L{ ?x . ?ys } ?p ?n } --
[ ?a length ?n < ]
[ ?a ?v prefix :>> ?b ]
|
{ ExpandQuot ?q ?b ?ys ?p ?n } ;

! NOTE: only fully expanded macros are treated
CHR: expand-macro @ // { ExpandQuot ?q ?a ?i ?x ?n } -- [ ?a length ?n = ]
[ ?a ?q with-datastack first :>> ?p ]
|
! This should cause the current MakeEffect to be suspended, infer expansion
{ ?DeferTypeOf ?p ?sig }
! And return here...
{ Instance ?x ?sig }
    ;

CHR: known-slot-num @ { Eq ?n A{ ?a } } // { Slot ?o ?n ?v } -- |
{ Slot ?o ?a ?v } ;

CHR: known-instance @ { Eq ?c A{ ?d } } // { Instance ?x ?c } -- [ ?c term-var? ]
| { Instance ?x ?d } ;

CHR: known-declared-instance @ { Eq ?c A{ ?d } } // { DeclaredInstance ?x ?c } --
| { DeclaredInstance ?x ?d } ;

CHR: known-not-instance @ { Eq ?c A{ ?d } } // { DeclaredNotInstance ?x ?c } --
| { DeclaredNotInstance ?x ?d } ;

CHR: known-tag-num @ { Eq ?n A{ ?v } } // { Tag ?c ?n } -- |
{ Tag ?c ?v } ;


CHR: known-expr-val @ { Eq ?n A{ ?v } } // AS: ?p <={ expr-pred } -- [ ?n ?p vars in? ]
|
[ ?p { { ?n ?v } } lift* ] ;

! *** Slot conversion
! TODO: this conversion can be wrong when working on numerically optimized code?
CHR: known-named-slot @ { Eq ?o A{ ?tau } } // { Slot ?o A{ ?n } ?v } -- [ ?tau tuple-class? ]
[ ?tau all-slots [ offset>> ?n = ] find nip :>> ?s ] [ ?s name>> :>> ?m ]
[ ?s class>> :>> ?rho ]
|
{ Slot ?o ?m ?v }
{ DeclaredInstance ?v ?rho } ;

CHR: known-boa-spec @ { Eq ?c A{ ?v } } // AS: ?p <={ Boa ?c ?i ?o } -- |
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
