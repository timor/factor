USING: accessors arrays chr.factor chr.factor.intra-effect.maps chr.factor.util
chr.parser chr.state classes classes.algebra classes.builtin classes.predicate
classes.singleton classes.tuple classes.tuple.private combinators
combinators.short-circuit continuations generic generic.single grouping kernel
kernel.private lists math math.functions math.order quotations sequences sets
slots slots.private sorting strings terms types.util words ;

IN: chr.factor.intra-effect


! * Simplification/Intra-Effect reasoning

CHRAT: chr-intra-effect { }

CHR: invalid-stays-invalid @ { Invalid } // { Invalid } -- | ;


! *** Mode-agnostic Normalizations
! ! TODO: big change: don't allow singleton value classes anymore, that messes with the class/value
! CHR: instance-of-wrapper @ {  }

! NOTE: Should be safe, as we don't define new stuff here if there is only one var?
CHR: comm-var-is-lhs @ // AS: ?p <={ symmetric-pred A{ ?l } ?v } -- [ ?v term-var? ] |
[ { ?v ?l } ?p class-of slots>tuple ] ;

! Not ideal.  If we do that, we mix value and type levels.
! CHR: literal-f-is-class-f @ // { Instance ?x W{ f } } -- | { Instance ?x POSTPONE: f } ;
! Same here
! CHR: literal-singleton-class-is-class @ // { Instance ?x ?tau } -- [ { ?tau } first wrapper? ] [ { ?tau } first wrapped>> :>> ?rho singleton-class? ] |
! { Instance ?x ?rho } ;
CHR: specialize-t-class @ { Eq ?x t } // { Instance ?x Is( not{ t } ?tau ) } --
[ ?tau t classes-intersect? ] | { Instance ?x t } ;

CHR: wrapper-type-is-eq @ // { Instance ?x Is( wrapper ?tau ) } --
[ { ?tau } first wrapped>> :>> ?v class-of :>> ?rho drop t ] |
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
{ ApplyEffect ?sig L{ ?x . ?b } L{ ?c . ?b } }
{ Instance ?c W{ t } }
{ DeclaredInstance ?x ?rho } ;

CHR: declared-not-predicate-class @ // { DeclaredNotInstance ?x A{ ?tau } } -- [ ?tau predicate-class? ]
[ ?tau class-not :>> ?rho ]
[ ?tau make-instance-check :>> ?q ]
|
{ Instance ?x ?rho }
{ ?DeferTypeOf ?q ?sig }
{ ApplyEffect ?sig L{ ?x . ?b } L{ ?c . ?b } }
{ Instance ?c W{ f } } ;

CHR: normalize-known-not-declaration @ // { DeclaredNotInstance ?x A{ ?tau } } -- [ { ?tau } first classoid? ]
[ { ?tau } first class-not :>> ?sig ] |
{ DeclaredInstance ?x ?sig } ;

CHR: declaration-is-assertion @ // { DeclaredInstance ?x A{ ?tau } } -- |
{ Instance ?x ?tau } ;

! *** Same Parameters
! Relations that define the same parameter when there twice.  True for Composition and Phi Mode

CHR: same-length-is-same @ { Length ?a M{ ?n } } // { Length ?a M{ ?m } } -- | [ ?m ?n ==! ] ;
CHR: same-length-is-eql @ { Length ?a ?n } { Length ?a ?m } // -- | { Eql ?n ?m } ;

! ! Flatten union classes for now.
! CHR: flatten-union-instance @ // { Instance ?x A{ ?tau } } -- [ { ?tau } first :>> ?rho union-class? ] |
! [| | ?rho flatten-class <anonymous-union> :> c
!  { Instance ?x c }
! ] ;

CHR: early-exit @ { Invalid } // <={ body-pred } -- | ;
CHR: early-exit-liveness @ { Invalid } // <={ liveness-pred } -- | ;
CHR: early-exit-deferred-inference @ { Invalid } // <={ ?DeferTypeOf } -- | ;

! *** <Phi
PREFIX-RULES: { P{ PhiMode } }

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

CHR: already-decider @ { Decider ?x } // <={ Discriminator ?y } -- [ ?x vars ?y vars set= ] | ;
CHR: already-discriminator @ { Discriminator ?x } // { Discriminator ?y } -- [ ?x vars ?y vars set= ] | ;

! NOTE: Changing the decider logic to include the whole pred
! CHR: destruc-decider @ // { Decider ?x } -- [ ?x sequence? ] |
! [ ?x [ term-var? ] filter [ Decider boa ] map ] ;

! CHR: destruc-discriminator @ // { Discriminator ?x } -- [ ?x sequence? ] |
! [ ?x [ term-var? ] filter [ Discriminator boa ] map ] ;

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
! too sensitive?  Trying that approach...
! Basic idea: if there is at least one observable value which, when known™ will definitely make exactly one of the
! two predicates fail, and there is at least one other observable value which will have a limited value range in one pred
! than the other, then we treat the type as being parameterized in the deciding value.
CHR: have-interesting-decider @ { MakeEffect ?i ?o ?l __ __ } // <={ Discriminator ?x } { Decider ?y }
-- [ ?i vars ?o vars append ?l vars union [ ?x vars swap subset? ] [ ?y vars swap subset? ] bi and ] | { Invalid } ;

! *** Phi Predicate Handling

! NOTE: this takes this out of the reasoning.  However, anything that should be able to be reasoned
! from the existence of same information different branches should have done during composition already.
! After this rule, existence of predicates is assumed to be only present in one branch.
CHR: phi-same-branch-pred @ // AS: ?p <={ body-pred } AS: ?p <={ body-pred } -- | { Collect ?p } ;
! TODO: test
CHR: phi-same-symmetric-pred @ // AS: ?p <={ symmetric-pred ?x ?y } AS: ?q <={ symmetric-pred ?y ?x } -- [ ?p ?q [ class-of ] same? ] |
{ Collect ?p } ;

CHR: phi-same-sum-result-1 @ { Sum ?z ?x ?y } { Sum ?a ?x ?y } // -- | [ ?z ?a ==! ] ;
CHR: phi-same-prod-result-1 @ { Prod ?z ?x ?y } { Prod ?a ?x ?y } // -- | [ ?z ?a ==! ] ;

! NOTE: This assumes covariant tuple semantics for all expr preds! If there really is a non-overlapping value,
! It must be caught in another pred!
CHR: phi-specialized-expr-pred @ // AS: ?p <={ expr-pred } AS: ?q <={ expr-pred } -- [ ?p ?q [ class-of ] same? ]
[ ?p ?q more-general-pred :>> ?r ] | { Collect ?r } ;

! XXX: this is not correct because it could set different access depth equal by equating internal values with inputs/outputs.
! This would probably need to be solved by a complete isomorphism checker on the internal structure?
! CHR: phi-same-slot-must-be-same-var @ { Slot ?o ?n M{ ?v } } { Slot ?o ?n M{ ?w } } // -- | [ ?v ?w ==! ] ;
! CHR: phi-same-obj-slot-is-same-loc @ { SlotLoc ?x ?o ?n } { SlotLoc ?y ?o ?n } // -- | [ ?y ?x ==! ] ;

! FIXME: follow-up location stuff phi-ing.  Possibly completely loop the locop states in slot reads?
! Again, the assumption here is basically graph matching.  For circular locops, this should not
! introduce any ambiguity in the case of multiple reads since those are resolved?
! Might have to normalize any ..a pop ..a -> ..a push ..b / ..a pop ..b -> ..b push ..b combinations though...
! FIXME: Losing unresolved loc-ops in phi branches needs to resolve the states?
CHR: phi-same-loc-pop-item-and-next-state @ { LocPop ?x ?a ?v ?b ?l __ } { LocPop ?x ?a ?w ?c ?l __ } // -- [ ?c ?b == not ] [ ?a ?b == not ] [ ?c ?a == not ] |
[ ?b ?c ==! ] [ ?v ?w ==! ] ;

CHR: phi-disjoint-instance-decider @ { Instance ?x A{ ?rho } } { Instance ?x A{ ?tau } } // --
[ { ?rho ?tau } first2 classes-intersect? not ] | { Decider ?x } ;

CHR: phi-maybe-disjoint-instance @ { Instance ?x A{ ?rho } } { Instance ?x A{ ?tau } } // --
[ { ?rho ?tau } first2 { [ classes-intersect? ] [ class= not ] } 2&& ] | { Discriminator ?x } ;

! TODO: might not be good to use simplifying-class-or here?
CHR: phi-union-instance @ // { Instance ?x A{ ?rho } } { Instance ?x A{ ?tau } } --
[ { ?rho ?tau } first2 simplifying-class-or :>> ?sig ] | { Collect P{ Instance ?x ?sig } } ;

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

! ! **** phi union types

! Slots
! CHR: phi-slot @ { Phi ?z ?x } { Phi ?z ?y } // { Slot ?x ?n ?a } { Slot ?y ?n ?b } -- |
! { Phi ?c ?a } { Phi ?c ?b } { Slot ?z ?n ?c } ;

! **** Relational reasoning

CHR: phi-eq-decider @ { Eq ?x A{ ?b } } { Eq ?x A{ ?c } } // -- [ ?b ?c eq? not ] |
{ Decider ?x } ;
CHR: phi-eql-decider @ { Eql ?x A{ ?b } } { Eql ?x A{ ?c } } // -- [ ?b ?c = not ] |
{ Decider ?x } ;
: order? ( obj1 obj2 -- min max ? )
    [ 2dup <=> +gt+ eq? [ swap ] when t ] [ drop f ] recover ;
CHR: phi-eq-range @ // { Eq ?x A{ ?b } } { Eq ?x A{ ?c } } -- [ ?b ?c order? [ :>> ?n drop :>> ?m drop ] dip ]
|
{ Collect P{ Le ?m ?x } }
{ Collect P{ Le ?x ?n } } ;
! TODO: abstract to all relations somehow

! NOTE: replacing these with discriminators for now.  The idea is that this is not an observable single-value
! difference thing in the input or output?
! CHR: phi-eq-neq-1 @ { Eq ?x ?y } { Neq ?x ?y } // -- | { Decider { ?x ?y } } ;
! CHR: phi-eq-neq-2 @ { Eq ?x ?y } { Neq ?y ?x } // -- | { Decider { ?x ?y } } ;
CHR: phi-eq-neq-1 @ <={ Eql ?x ?y } { Neq ?x ?y } // -- | { Discriminator { ?x ?y } } ;
CHR: phi-eq-neq-2 @ <={ Eql ?x ?y } { Neq ?y ?x } // -- | { Discriminator { ?x ?y } } ;
! CHR: phi-neq-is-always-decider @ { Neq ?x ?y } // -- | { Decider { ?x ?y } } ;

CHR: phi-eql-eq-1 @ { Eql ?x ?y } { Eq ?x ?y } // -- | { Discriminator { ?x ?y } } { Collect P{ Eql ?x ?y } } ;
CHR: phi-eql-eq-2 @ { Eql ?x ?y } { Eq ?x ?y } // -- | { Discriminator { ?x ?y } } { Collect P{ Eql ?x ?y } } ;

! CHR: phi-eq-lt-decider-1 @ // { Eq ?x ?y } { Lt ?x ?y } -- | { Decider { ?x ?y } } { Keep P{ Le ?x ?y } } ;
! CHR: phi-eq-lt-decider-2 @ // { Eq ?x ?y } { Lt ?y ?x } -- | { Decider { ?x ?y } } { Keep P{ Le ?y ?x } } ;
CHR: phi-eq-lt-discrim-1 @ // <={ Eql ?x ?y } { Lt ?x ?y } -- | { Discriminator { ?x ?y } } { Collect P{ Le ?x ?y } } ;
CHR: phi-eq-lt-discrim-2 @ // <={ Eql ?x ?y } { Lt ?y ?x } -- | { Discriminator { ?x ?y } } { Collect P{ Le ?y ?x } } ;

CHR: phi-eq-le-discrim-1 @ // <={ Eql ?x ?y } { Le ?x ?y } -- | { Discriminator { ?x ?y } } { Collect P{ Le ?x ?y } } ;
CHR: phi-eq-le-discrim-2 @ // <={ Eql ?y ?x } { Le ?x ?y } -- | { Discriminator { ?x ?y } } { Collect P{ Le ?x ?y } } ;

! CHR: phi-lt-lt-decider @ // { Lt ?x ?y } { Lt ?y ?x } -- | { Decider { ?y ?x } } ;
CHR: phi-lt-lt-decider @ { Lt ?x ?y } { Lt ?y ?x } // -- | { Discriminator { ?x ?y } } ;

! CHR: phi-lt-le-decider @ // { Lt ?x ?y } { Le ?y ?x } -- | { Discriminator { ?x ?y } } ;
CHR: phi-lt-le-decider @ { Lt ?x ?y } { Le ?y ?x } // -- | { Decider { ?x ?y } } ;

! These are overlapping, so no deciders
CHR: phi-discrim-le-lt @ { Le ?x ?v } { Lt ?v ?x } // -- | { Discriminator { ?x ?v } } ;
! CHR: phi-discrim-le-rhs @ { Le ?v ?x } { Lt ?x ?v } // -- [ ?x term-var? ] | { Discriminator ?x } ;

! FIXME: seems to be unnecessary right now, need to test for this being a decider and not a discriminator
! ! Definitely disjoint numerical ranges, equality or not
! CHR: phi-le-le-decider @ <={ Le ?x A{ ?m } } <={ Le A{ ?n } ?x } // -- [ ?m ?n < ] | { Decider ?x } ;

! *** Phi-Mode single-branch predicates

! These are basically non-surviving single-branch variants
! The idea is that they do specify an aspect which only a part of the values of
! the other side would satisfy
CHR: phi-rel-discriminates @ <={ rel-pred ?x ?y } // -- | { Discriminator { ?x ?y } } ;

! *** Phi Math

CHR: phi-keep-commutative-pred @ // AS: ?p <={ commutative-op ?z ?x ?y } AS: ?q <={ commutative-op ?z ?y ?x } --
[ ?p ?q [ class-of ] same? ] | { Collect ?p }  ;

! NOTE: There's a load of these, really... maybe only do that if we
! need parameters?  Have to be careful to not generate too many
! new dependencies in e.g. loop handling!  Alternatively, only use
! these things in phi reasoning?  Yeah, seems to be better...
! TODO: generalize
CHR: eq-propagate-sum-1 @ { Eq ?x ?y } { Sum ?a ?y ?b } // -- |
{ Sum ?a ?x ?b } ;


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


! **** phi recursive calls

! We don't merge call-recursives for our own disjoint definition
CHR: phi-call-rec-self @ { PhiSchedule ?w __ __ } //
{ CallRecursive ?w __ __ } -- | { Invalid } ;

! **** Conditions under which even a single pred can conserve disjunctivity
! CHR: disj-output-maybe-callable @ { MakeEffect __ ?b __ __ __ } // { Instance ?x A{ ?tau } } --
! [ ?x ?b vars in? ] [ { ?tau } first classoid? ] [ { ?tau } first callable classes-intersect? ] | { Invalid } ;

! CHR: disj-param-maybe-callable @ <={ MakeEffect } { Params ?l } // { Instance ?x A{ ?tau } } --
! [ ?x ?l in? ] [ { ?tau } first classoid? ] [ { ?tau } first callable classes-intersect? ] | { Invalid } ;

! CHR: disj-apply-unknown-effect @ <={ MakeEffect } // { ApplyEffect M{ ?tau } __ __ } -- | { Invalid } ;

! TODO: need?
CHR: disj-is-macro-effect @ <={ MakeEffect } // { MacroExpand __ __ __ __ } -- | { Invalid } ;

! NOTE: this is pretty eager, as it will preserve all higher-order parametrism explicitly
CHR: disj-is-inline-effect @ <={ MakeEffect } // <={ CallEffect ?p . __ } -- | { Invalid } ;

CHR: disj-unresolved-generic @ <={ MakeEffect } // <={ GenericDispatch } -- | { Invalid } ;
CHR: disj-unresolved-prim-call @ <={ MakeEffect } // <={ PrimCall } -- | { Invalid } ;
! FIXME: combine phi and comp phases better!  Collection an liveness needs to be way improved!

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

PREFIX-RULES: { P{ CompMode } }
! TERM-VARS: ?ctx ;
! MODIFY: [ [ ?ctx swap CP boa ] map ]

CHR: invalid-defer-type-request @ // { ?DeferTypeOf ?x __ } -- [ ?x callable? not ] | [ { ?x "not a valid thing to infer" } throw ] ;

: same-state? ( x y -- ? ) [ lastcdr ] same? ;


! Possibly expensive? Seems like it! But some are definitely needed, e.g. for Eq, aaand for Le
! CHR: unique-val-pred @ AS: ?p <={ val-pred } // AS: ?p <={ val-pred } -- | ;
! TODO include num=
CHR: var-eq-is-true @ // <={ Eql M{ ?x } ?x } -- | ;
CHR: unique-eq-pred-1 @ { Eq M{ ?x } M{ ?y } } // { Eq M{ ?x } M{ ?y } } -- | ;
CHR: unique-eq-pred-2 @ { Eq M{ ?x } M{ ?y } } // { Eq M{ ?y } M{ ?x } } -- | ;
CHR: eq-must-be-same-literal-1 @ { Eq M{ ?x } A{ ?a } } // { Eq M{ ?x } M{ ?y } } -- | [ ?x ?y ==! ] ;
CHR: eq-must-be-same-literal-2 @ { Eq M{ ?x } A{ ?a } } // { Eq M{ ?y } M{ ?x } } -- | [ ?x ?y ==! ] ;
CHR: eq-literal-must-be-same-var @ { Eq M{ ?x } A{ ?a } } // { Eq M{ ?y } A{ ?b } } -- [ ?a local-alloc-val? ] [ ?a ?b eq? ] | [ ?x ?y ==! ] ;
CHR: unique-notsame-pred1 @ { NotSame ?x ?y } // { NotSame ?x ?y } -- | ;
CHR: unique-notsame-pred2 @ { NotSame ?x ?y } // { NotSame ?y ?x } -- | ;
CHR: unique-instance @ { Instance ?x ?tau } // { Instance ?x ?tau } -- | ;
CHR: unique-le-pred @ { Le ?x ?y } // { Le ?x ?y } -- | ;
CHR: unique-lt-pred @ { Lt ?x ?y } // { Lt ?x ?y } -- | ;
CHR: unique-slot-pred @ { Slot ?o ?n ?v } // { Slot ?o ?n ?v } -- | ;
CHR: unique-allocation-pred @ { LocalAllocation ?a ?o } // { LocalAllocation ?b ?o } -- [ ?a ?b same-state? ] [ ?a llength* ?b llength* <= ] | ;

! CHR: unique-equiv @ { <==> ?c ?p } // { <==> ?c ?p } -- | ;
! CHR: assume-equiv-true @ { <==> ?c ?p } { Instance ?c A{ ?tau } } // --
! [ ?tau \ f classes-intersect? not ] | [ ?p ] ;
! CHR: assume-equiv-false @ { <==> ?c ?p } { Instance ?c A{ ?tau } } // --
! [ ?tau t classes-intersect? not ] | [ ?p opposite-predicate ] ;

! NOTE: this is taken directly from the definition of = !
! TODO: Make sure this does not mess anything up!
CHR: eq-class-eq-is-same @ { Instance ?x Is( classoid ?rho ) } // { Instance ?y Is( classoid ?tau ) } { Eq M{ ?x } M{ ?y } } --
[ ?rho union{ word fixnum } class<= ] [ ?rho ?tau class= ]
| [ ?x ?y ==! ] ;

! FIXME: This treats all integers as fixnums with regards to expression reasoning.  This should be fine as long as we don't reason
! about bignum implementation details?
CHR: integer-num=-is-eq @ { Instance ?x A{ ?c } } { Instance ?y A{ ?d } } // { Num= ?x ?y } -- [ ?c integer class<= ] [ ?d integer class<= ] |
{ Eq ?x ?y } ;

! ! NOTE: currently only known to be needed for bignum exception. Might make sense
! ! to eliminate that distinction for reasoning?  Inside the "bignum" processing closure, should
! ! stay correct though!
! ! FIXME: find some way to automate this.  Either on rule level, or on head level!
! ! Applies to all numeric predicate holes.
! CHR: eq-propagates-nth-n-1 @ { Eq ?n ?m } { Nth ?v ?a ?n } // -- |
! { Nth ?v ?a ?m } ;
! CHR: eq-propagates-nth-n-2 @ { Eq ?m ?n } { Nth ?v ?a ?n } // -- |
! { Nth ?v ?a ?m } ;

! NOTE: the reasoning is that this can inductively only happen during composition of two straight-line
! effects. So the instance in the first one is a "provide", and the instance in the second one is an "expect".
! Since the intersection type operation is commutative, we don't care which came from which.
! FIXME: The rule should also apply to Phi Mode reasoning, but for a different reason.
CHR: same-slot-must-be-same-var @ { Slot ?o ?n M{ ?v } } // { Slot ?o ?n M{ ?w } } -- | [ ?v ?w ==! ] ;
! CHR: same-slot-must-be-eq @ { Slot ?o ?n ?v } { Slot ?o ?n ?w } // -- | { Eq ?v ?w } ;

: typeof>tag ( quoted -- n/f )
    first
    {
        { [ dup wrapper? ] [ wrapped>> tag ] }
        { [ dup tuple-class? ] [ drop tuple class>type ] }
        { [ dup class? ] [ class>type ] }
        [ drop f ]
    } cond ;

! *** Math Conversions
CHR: math-call-plus @ // { MathCall + { ?x ?y } { ?z } } -- |
{ Instance ?z number } { Sum ?z ?x ?y } ;
CHR: math-call-minus @ // { MathCall - { ?x ?y } { ?z } } -- |
{ Instance ?z number } { Sum ?x ?y ?z } ;
CHR: math-call-mul @ // { MathCall * { ?x ?y } { ?z } } -- |
{ Instance ?z number } { Prod ?z ?x ?y } ;
CHR: math-call-div @ // { MathCall / { ?x ?y } { ?z } } -- |
{ Instance ?z number } { Prod ?x ?y ?z } ;

! *** Instance reasoning
! Tags are an implementation detail, and are re-converted to classes as soon as possible
CHR: check-tag @ { Instance ?x A{ ?v } } // { Tag ?x A{ ?n } } -- [ { ?v } typeof>tag :>> ?m ] |
[ ?m ?n = f { Invalid } ? ] ;

CHR: literal-defines-tag @ { Instance ?x A{ ?v } } { Tag ?x ?n } // -- [ { ?v } typeof>tag :>> ?m ]
[ ?v tag :>> ?m ] | { Instance ?n W{ ?m } } ;

CHR: convert-tag @ // { Tag ?x A{ ?n } } -- [ ?n type>class :>> ?tau ] |
{ Instance ?x ?tau } ;

CHR: instance-of-non-classoid @ { Instance ?x A{ ?c } } // -- [ { ?c } first classoid? not ] | { Invalid } ;
! NOTE: this shouldn't ever happen!
CHR: check-lit-instance @ // { Instance A{ ?v } A{ ?c } } -- | [ "bogus rule check-lit-instance" throw ]
[ ?v ?c instance? f P{ Invalid } ? ] ;
CHR: invalid-eq-instance @ // { Instance ?x A{ ?c } } { Eq ?x A{ ?v } } -- [ ?v ?c instance? not ] | { Invalid } ;

CHR: null-instance-is-invalid @ // { Instance ?x null } -- | { Invalid } ;

! NOTE: There are two ways to handle intersections: in factor's type system in
! the intersection instance type, or in the
! implicit conjunction of the constraint store.  Currently, this is put into the
! intersection classes of the factor type system.

! NOTE: effect of this rule on final performance is unclear at the moment
CHR: instance-subsumption @ { Instance ?x Is( classoid ?tau ) } // { Instance ?x Is( classoid ?sig ) } --
[ ?tau ?sig class<= ] | ;
CHR: instance-intersection @
// { Instance ?x A{ ?tau } } { Instance ?x A{ ?sig } } --
! NOTE: with lazy dispatch, this destroys nominative types
! [ { ?tau ?sig } first2 simplifying-class-and :>> ?c ] |
[ { ?tau ?sig } first2 class-and :>> ?c ] |
{ Instance ?x ?c } ;

CHR: instance-intersect-effect @ { Instance ?x ?e }
// { Instance ?x A{ ?tau } } --
[ ?e valid-effect-type? ] |
[ ?tau callable classes-intersect?
 f { Invalid } ? ] ;

! **** Class relations
! from (clone) y is the output, x is the input
! CHR: specialize-class=-forward @ { Instance ?x Is( classoid ?tau ) } { ClassPred ?y ?x class= } { Instance ?y Is( classoid ?sig ) } // --
! [ ?sig ?tau class= not ] | { Instance ?y  }

! in: object, out: array -> don't change
! in: object, out: object -> don't change
! in: array, out: object -> out: array & object
! in: string, out: array -> out: array & string
! output class <= input class -> don't change.  Intersect otherwise
! TODO possibly translate into symmetric class<= constraints
CHR: specialize-class=-forwards @ { ClassPred ?y ?x class= } { Instance ?x Is( classoid ?tau ) } // { Instance ?y Is( classoid ?sig ) } --
[ ?sig ?tau class<= not ] [ ?sig ?tau class-and :>> ?rho ] | { Instance ?y ?rho } ;

CHR: specialize-class=-backwards @ { ClassPred ?y ?x class= } { Instance ?y Is( classoid ?tau ) } // { Instance ?x Is( classoid ?sig ) } --
[ ?sig ?tau class<= not ] [ ?sig ?tau class-and :>> ?rho ] | { Instance ?x ?rho } ;

CHR: redundant-final-class= @ { Instance ?x Is( classoid ?rho ) } { Instance ?y Is( classoid ?rho ) } // { ClassPred ?y ?x class= }
-- [ ?rho final-data-class? ] | ;

! TODO: in-between forms also!
CHR: check-literal-class-pred @ // { ClassPred A{ ?y } A{ ?x } class= } -- | [ ?y ?x [ class-of ] same? f P{ Invalid } ? ] ;

CHR: eq-defines-class @ { Eq M{ ?x } M{ ?y } } // { Instance ?x Is( classoid ?rho ) } { Instance ?y Is( classoid ?tau ) } --
[ { ?rho ?tau } first2 class= not ] [ { ?rho ?tau } first2 class-and :>> ?sig ] | { Instance ?x ?sig } { Instance ?y ?sig } ;

! *** Arithmetics
CHR: check-eql-lit @ // { Eql A{ ?a } A{ ?b } } -- | [ ?a ?b = f P{ Invalid } ? ] ;
CHR: eq-class-eql-is-eq-pred @ // { Eql ?x Is( union{ fixnum word } ?o ) } -- | { Eq ?x ?o } ;

CHR: check-le @ // { Le A{ ?x } A{ ?y } } -- | [ ?x ?y <= f P{ Invalid } ? ] ;
CHR: check-lt @ // { Lt A{ ?x } A{ ?y } } -- | [ ?x ?y < f P{ Invalid } ? ] ;
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
! CHR: check-eq @ // { Eq A{ ?x } A{ ?y } } -- | [ ?x ?y eq? f P{ Invalid } ? ] ;
CHR: check-eq @ { Eq ?x A{ ?a } } // { Eq ?x A{ ?b } } -- | [ ?a ?b eq? f P{ Invalid } ? ] ;
CHR: local-alloc-never-eq-1 @ // { Eq M{ ?x } M{ ?y } } { LocalAllocation __ ?x } -- | { Invalid } ;
CHR: local-alloc-never-eq-2 @ // { Eq M{ ?x } M{ ?y } } { LocalAllocation __ ?y } -- | { Invalid } ;
CHR: check-eql-neq-1 @ // { Eql ?x ?y } { Neq ?x ?y } -- | { Invalid } ;
CHR: check-eql-neq-2 @ // { Eql ?x ?y } { Neq ?y ?x } -- | { Invalid } ;
! NOTE: neq has eql sematics!
CHR: check-neq @ // { Neq A{ ?x } A{ ?y } } -- | [ ?x ?y = P{ Invalid } f ? ] ;
! NOTE: might be careful about the following if the (implementation-detail) disjointness of eq? vs equal? definitions
! is needed?
CHR: neq-same-var @ // <={ Neq M{ ?x } M{ ?x } } -- | { Invalid } ;
! NOTE: this might not be possible to correctly check because of substitution?
! A neuralgic case could be literals, actually
! CHR: check-notsame @ { Eq ?x A{ ?a } } { Eq ?y A{ ?b } } // { NotSame ?x ?y } -- | [ ?a ?b eq? P{ Invalid } f ? ] ;
CHR: check-notsame @ // { NotSame A{ ?x } A{ ?y } } -- | [ ?x ?y eq? P{ Invalid } f ? ] ;
! FIXME: that is wrong: CHR: neq-subsumes-not-same @ { Neq ?x ?y } // { NotSame ?x ?y } -- | ;
! CHR: not-same-var @ // { NotSame ?x ?x } -- | { Invalid } ;
! TODO: make sure this doesn't break reasoning in phis
CHR: redundant-literal-neq @ { Instance ?x ?c } // { Neq ?x A{ ?l } } --
[ { ?l } first class-of ?c classes-intersect? not ] | ;
CHR: redundant-neq-instance @ { Instance ?x A{ ?c } } { Instance ?y A{ ?d } } //
{ Neq ?x ?y } -- [ { ?c ?d } first2 classes-intersect? not ] | ;

CHR: check-sum @ // { Sum A{ ?z } A{ ?x } A{ ?y } } -- [ ?x ?y + ?z = not ] | P{ Invalid } ;
! CHR: zero-sum-1 @ // { Sum ?z 0 ?y } -- | [ ?z ?y ==! ] ;
! CHR: zero-sum-2 @ // { Sum ?z ?x 0 } -- | [ ?z ?x ==! ] ;
! This should be fine, as we only swap between output holes
CHR: normalize-commutative-op @ // AS: ?p <={ commutative-op ?z A{ ?x } ?y } -- [ ?y term-var? ] |
[ { ?z ?y ?x } ?p class-of slots>tuple ] ;

CHR: neutral-sum-defines-eq @ // { Sum ?z ?x 0 } -- | { Eq ?z ?x } ;

! Anything more complex than that needs a linear equation predicate, or
! a linear solver, for that matter...
! TODO reactivate once confirmed that these aren't necessary for liveness
CHR: elim-transitive-literal-sum @ // { Sum ?z ?x A{ ?m } } { Sum ?x ?a A{ ?n } } --
[ ?z ?x == not ] [ ?m ?n + :>> ?k ] | { Sum ?z ?a ?k } ;
CHR: elim-transitive-literal-sum-diff-1 @ // { Sum ?z ?x A{ ?m } } { Sum ?z ?a A{ ?n } } --
[ ?m ?n - :>> ?k ] | { Sum ?a ?x ?k } ;

CHR: elim-transitive-literal-prod-mul @ // { Prod ?z ?x A{ ?m } } { Prod ?x ?a A{ ?n } } --
[ ?z ?x == not ] [ ?m ?n * :>> ?k ] | { Prod ?z ?a ?k } ;
CHR: elim-transitive-literal-prod-div-1 @ // { Prod ?x ?z A{ ?m } } { Prod ?a ?z A{ ?n } } -- [ ?m ?n >= ]
[ ?m ?n / :>> ?k ] | { Prod ?x ?a ?k } ;
! CHR: elim-transitive-literal-prod-div-2 @ // { Prod ?z ?x A{ ?n } } { Prod ?z ?a A{ ?m } } -- [ ?m ?n >= ]
! [ ?m ?n / :>> ?k ] | { Prod ?x ?a ?k } ;

! TODO: lt
CHR: transitive-le-ge @ { Le ?x ?y } { Le ?y ?z } // -- | { Le ?x ?z } ;
CHR: transitive-le-gt @ { Lt ?x ?y } { Le ?y ?z } // -- | { Lt ?x ?z } ;

! NOTE: This does not work naively for products!
! TODO: might need revisiting after being more explicit with math types and equality
! FIXME: automate
CHR: lit-sum-specializes-math-class-1 @ { Sum M{ ?z } ?x A{ ?m } } { Instance ?x ?c } // --
[ ?m class-of ?c pessimistic-math-class-max :>> ?d ] |
{ Instance ?z ?d } ;

! CHR: lit-sum-specializes-math-class-2 @ { Sum ?z ?x A{ ?m } } { Instance ?z ?c } // --
! [ ?m class-of ?c pessimistic-math-class-max :>> ?d ] |
! { Instance ?x ?d } ;

CHR: define-sum @ // { Sum ?z A{ ?x } A{ ?y } } --
[ ?x ?y + <wrapper> :>> ?v ] | { Instance ?z ?v } ;
CHR: define-diff-1 @ // { Sum A{ ?z } ?x A{ ?y } } --
[ ?z ?y - <wrapper> :>> ?v ] | { Instance ?x ?v } ;
CHR: define-diff-2 @ // { Sum A{ ?z } A{ ?y } ?x } --
[ ?z ?y - <wrapper> :>> ?v ] | { Instance ?x ?v } ;

CHR: check-prod @ // { Prod A{ ?z } A{ ?x } A{ ?y } } -- [ ?x ?y * ?z = not ] | P{ Invalid } ;
CHR: neutral-prod-1 @ // { Prod ?z 1 ?y } -- [ ?z term-var? ] [ ?y term-var? ] | [ ?z ?y ==! ] ;
CHR: neutral-prod-2 @ // { Prod ?z ?x 1 } -- [ ?z term-var? ] [ ?x term-var? ] | [ ?z ?x ==! ] ;
CHR: zero-prod-1 @ // { Prod ?z 0 ?y } -- | { Instance ?z 0 } ;
CHR: zero-prod-2 @ // { Prod ?z ?y 0 } -- | { Instance ?z 0 } ;
CHR: define-prod @ // { Prod ?z A{ ?x } A{ ?y } } --
[ ?x ?y * <wrapper> :>> ?v ] | { Instance ?z ?v } ;
CHR: define-frac-1 @ // { Prod A{ ?z } ?x A{ ?y } }  --
[ ?z ?y / <wrapper> :>> ?v ] | { Instance ?x ?v } ;
CHR: define-frac-2 @ // { Prod A{ ?z } A{ ?y } ?x }  --
[ ?z ?y / <wrapper> :>> ?v ] | { Instance ?x ?v } ;

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
CHR: apply-regular-effect @ // { ApplyEffect ?x ?i ?o } -- [ ?x Effect? ]
[ ?x fresh-effect :>> ?e ]
[ ?e in>> :>> ?c drop
  ?e out>> :>> ?d drop
  ?e preds>> :>> ?l drop
  t ] |
[ { ?i ?o } { ?c ?d } ==! ]
[ ?l ] ;

CHR: defer-apply-xor-effect @ // { ApplyEffect ?x ?i ?o } -- [ ?x Xor? ] [ ?x fresh-effect :>> ?y ] |
{ CallXorEffect ?y ?i ?o } ;

! NOTE: These only meet in renamed form?
! Probably not. [ ... ] [ call ] keep looks fishy...
! NOTE: big change: make a fresh effect before every call
! TODO: since we do that here, remove a lot of other fresh-effects....
CHR: call-applies-effect @ { Instance ?q ?x } // { CallEffect ?q ?a ?b } -- [ ?x valid-effect-type? ] |
{ ApplyEffect ?x ?a ?b } ;

! NOTE: this does not work right now mid-effect because of sequencing the body.
CHR: literal-call-type-must-be-known @ <={ FinishEffect } // { CallEffect ?q __ __ } { Eq ?q A{ ?p } }
! { Instance ?q ?rho } -- [ ?rho valid-effect-type? not ]
--
| [ { ?p "literal-effect-unknown" } throw ] ;

CHR: call-mode-error @ // { CallEffect A{ ?q } ?a ?b } -- | [ { ?q "call mode error" } throw ] ;

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
! CHR: call-applies-xor-effect @ { Instance ?q P{ Xor ?c ?d } } // { CallEffect ?q ?a ?b } -- |
! { CallXorEffect P{ Xor ?c ?d } ?a ?b } ;

! *** TODO Recursive Iteration expansion

CHR: call-recursive-eliminated @ // { CallRecursive null __ __ } -- | { Invalid } ;

CHR: call-recursive-canonical @ { TypeOfWord ?w ?rho } // { CallRecursive ?w ?i ?o } --
[ ?rho full-type? ] [ ?rho canonical? ] |
{ ApplyEffect ?rho ?i ?o } ;

! P{ CallRecursive tag ?a ?b } holds the enter-in stack in ?a
! iterated approach:
! tag -prelude-> ?a -RecursionTypePre-> ?b =same-layout-as= ?c -RecursionTypePost-> -FixPointCondition-> ?d
! NOTE: current layout: initial var_n, var_1, var_0
! It may be necessary to change this to var_n , var_n-m , var_n-m-1 , var_0
CHR: break-recursive-iteration @ { Iterated ?w ?a ?b ?c ?d __ } // { CallRecursive ?w ?i ?o } --
|
[ ?c ?i ==! ] ;

! NOTE: Idea: create an iteration constraint.  Should only be active in subsequent compositions
CHR: call-recursive-iteration @ { FixpointTypeOf ?w ?rho } { RecursionTypeOf ?w ?sig } //
{ CallRecursive ?w ?i ?o } --
[ ?rho full-type? ]
[ ?sig full-type? ]
[ ?i fresh :>> ?b ]
[ ?i fresh :>> ?c ] |
! ?i : recursive call input stack
! ?b : enter-out stack
! ?c : call-recursive in stack
! ?d : return-recursive out stack
! ?o : final call output stack
! FIXME: Instantiate in case of double recursion?
{ Iterated ?w ?i ?b ?c ?d ?o }
! Return Type call
{ ApplyEffect ?rho ?d ?o }
! { Instance ?q ?rho }
! { CallEffect ?q ?d ?o }
! Iteration Type call, don't match output
! { Instance ?p ?sig }
! { CallEffect ?p ?b ?x }
{ ApplyEffect ?sig ?b ?x }
{ LoopVar { ?i ?b ?c ?d } }
    ;

CHR: discard-known-iterated-stack @ // <={ Iterated __ . ?s } --
[ ?s list>array f lift [ same-state? ] monotonic? ] | ;

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

! TODO: The next approach is even more questionable, but the idea is that we have a monotone relation between
! Input and output, and we exactly know that we only take the exact same branch, then the monotonicity
! can be extended backwards (and forwards, for that matter?)
CHR: loop-instance-specialize-backwards @ { LoopVar { ?w ?x ?y ?z } }
{ Instance ?x A{ ?rho } } { Instance ?y A{ ?sig } } // -- [ ?rho ?sig class< ] |
{ Instance ?w ?rho } ;

! TODO: specialize forwards?

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
[ ?x ?y same-state? ] | { Invalid } ;

! **** Find Loop Counters
! TODO: Test if sum is always normalized for this? Nope, it doesnt
! Define Counters.  Note that These define _inclusive_ intervals, because
! If the sum is assumed to have been calculated, then the result is included
! CHR: loop-sum-defines-counters @ { Sum ?y ?x ?n } { LoopVar { ?w ?x ?y ?z } } // -- |
CHR: loop-sum-defines-plus-counter @ { Sum ?y ?x ?n } // { LoopVar { ?w ?x ?y ?z } } -- |
{ Counter ?w ?x ?y ?z ?n } ;

! FIXME: only works for literal sums right now
CHR: loop-sum-defines-minus-counter @ { Sum ?x ?y A{ ?n } } // { LoopVar { ?w ?x ?y ?z } } --
[ 0 ?n - :>> ?m ] |
{ Counter ?w ?y ?x ?z ?m } ;

! ! NOTE: the fact that this is necessary kind of stinks...
! ! TODO: may be better to keep LoopVars instead?
! CHR: have-counter-already @ { Counter ?x __ __ __ } // { Counter ?x __ __ __ } -- | ;

! NOTE: this will probably generate some noise in connection with the other instance loop bound
! propagation rule
CHR: loop-counter-input-stays-integer @ { Counter ?x ?a ?b ?y A{ ?m } }
{ Instance ?x ?c } // -- [ ?c integer class<= ] [ ?m integer? ] |
{ Instance ?a integer } { Instance ?b integer } { Instance ?y integer } ;
! [ ?c ?m class-of pessimistic-math-class-max :>> ?d ] |
! { Instance ?x ?d }
! { Instance ?b ?d } ;

! CHR: loop-counter-output-specializes @ { Counter ?x ?a ?b A{ ?m } }
! { Instance ?a ?c } // --
! [ ?c ?m class-of pessimistic-math-class-max :>> ?d ] |
! { Instance ?x ?d }
! { Instance ?b ?d } ;

! TODO cases for lt?
! If we now we are descending by constant amount m,
! then the final value can only be in m-range of a lower loop bound (Assuming we terminate!)
! NOTE: Not sure about that right now
! In particular, this applies to any Le predicate, while the intention of this was to only work
! on the lowest bound!
! CHR: tighten-loop-bound-desc @ { Counter ?x ?a ?b ?y A{ ?m } } { Le ?y A{ ?n } } // --
! [ ?m 0 < ]
! [ ?m 1 + ?n + :>> ?k ]
! | { Le ?k ?y } ;
! This version is trying to ensure that this only works on the end of the range...
CHR: tighten-loop-bound-desc @ { Counter ?x ?a ?b ?y A{ ?m } }
{ Le ?y A{ ?n } } { Le A{ ?n } ?b } // -- [ ?m 0 < ] [ ?m 1 + ?n + :>> ?k ] |
{ Le ?k ?y } ;
CHR: tighten-loop-bound-asc @ { Counter ?x ?a ?b ?y A{ ?m } }
{ Le ?b A{ ?n } } { Le A{ ?n } ?y } // -- [ ?m 0 > ] [ ?m 1 - ?n + :>> ?k ] |
{ Le ?y ?k } ;

! TODO: implement based on predicates on the step, too?
! CHR: known-down-counter-literal @ // { Counter ?x ?a ?b A{ ?n } } -- [ ?n 0 < ] |
! TODO: either replace like expr-pred, or add rules for non-lit case
CHR: known-down-counter-literal @ { Counter ?x ?a ?b ?y A{ ?v } } // -- [ ?v 0 < ] |
{ Le ?a ?x } { Le ?y ?b } ;

CHR: known-up-counter-literal @ { Counter ?x ?a ?b ?y A{ ?v } } // -- [ ?v 0 > ] |
{ Le ?x ?a } { Le ?b ?y } ;

CHR: integer-lt-is-le @ { Instance ?x ?c } // { Lt ?x A{ ?m } } -- [ ?c integer class<= ]
[ ?m 1 - ceiling >integer :>> ?k ] | { Le ?x ?k } ;

CHR: integer-gt-is-ge @ { Instance ?x ?c } // { Lt A{ ?m } ?x } -- [ ?c integer class<= ]
[ ?m 1 + floor >integer :>> ?k ] | { Le ?k ?x } ;

! TODO: the ge and lt equivalents?.  Class matcher would be nice...
CHR: le-offset-sum-1 @ { Sum ?y ?x A{ ?n } } { Le ?x A{ ?v } } // --
[ ?v ?n + :>> ?k ] | { Le ?y ?k } ;
CHR: le-offset-sum-2 @ { Sum ?x ?y A{ ?n } } { Le ?x A{ ?v } } // --
[ ?v ?n - :>> ?k ] | { Le ?y ?k } ;

! CHR: gt-offset-sum @ { Sum ?y ?x A{ ?n } } { Lt A{ ?v } ?x } // --
! [ ?n ?v + :>> ?k ] | { Lt ?k ?y } ;
CHR: ge-offset-sum-1 @ { Sum ?y ?x A{ ?n } } { Le A{ ?v } ?x } // --
[ ?v ?n + :>> ?k ] | { Le ?k ?y } ;
CHR: ge-offset-sum-2 @ { Sum ?x ?y A{ ?n } } { Le A{ ?v } ?x } // --
[ ?v ?n - :>> ?k ] | { Le ?k ?y } ;

! *** TODO Modular arithmetic
! Needed for fixed-width computations, possibly some loop analysis/transformation foo


! *** Calling Curry/Compose

! NOTE: Make sure this deferred inference request does not conflict with recursive call inference by
! introducing artificial recursion requests where there are none!
PREDICATE: callable-subclass < class callable class<= ;

CHR: infer-literal-callable @ { Eq ?q Is( callable ?v ) } // { Instance ?q Is( callable-subclass ?tau ) } -- [ ?v quote-literals :>> ?w ] |
{ ?DeferTypeOf ?w ?rho } { Instance ?q ?rho } ;

CHR: call-destructs-curry @ { Instance ?q curried } { Slot ?q "quot" ?p } { Slot ?q "obj" ?x } // { CallEffect ?q ?a ?b } -- |
{ CallEffect ?p L{ ?x . ?a } ?b } ;

CHR: call-destructs-composed @ { Instance ?p composed } { Slot ?p "first" ?q } { Slot ?p "second" ?r } // { CallEffect ?p ?a ?b } -- |
{ CallEffect ?q ?a ?rho } { CallEffect ?r ?rho ?b } ;

! *** Declarations
! TODO: why are there Ensure and Declare?
! Seems like Ensure is to be used with declaration order,
! While Declare is to be used with list-stack order, at the least.
! Another difference seems to be that Declare(Stack) is actually referring
! to values!


CHR: did-ensure @ // { Ensure +nil+ __ } -- | ;
CHR: did-declare @ // { Declare +nil+ __ } -- | ;
CHR: did-declare-stack @ // { DeclareStack +nil+ __ } -- | ;
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

CHR: known-declare-stack @
{ Eq ?l A{ ?tau } } // { DeclareStack ?l ?a } --
[ ?tau <reversed> >list :>> ?m ] | { Declare ?m ?a } ;


! *** Macro Expansion/Folding

! CHR: known-macro-quot @ // { MacroExpand ?w ?a ?i ?x } -- [ ?w macro-quot :>> ?q ]
! [ ?w macro-effect :>> ?n ] |
! { ExpandQuot ?q ?a ?i ?x ?n } ;

! CHR: known-macro-arg @ { Eq ?x A{ ?v } } // { ExpandQuot ?q ?a L{ ?x . ?ys } ?p ?n } --
CHR: known-macro-arg @ { Eq ?x A{ ?v } } // { MacroCall ?q ?a ?p } --
[ ?x ?a in? ] [ ?a { { ?x ?v } } lift* :>> ?b ] | { MacroCall ?q ?b ?p } ;
! [ ?a length ?n < ]
! [ ?a ?v prefix :>> ?b ]
! |
! { ExpandQuot ?q ?b ?ys ?p ?n } ;

! NOTE: only fully expanded macros are treated
! TODO: maybe rewrite to not let the calleffect linger before?  This would only be useful
! if we want to reason about what the macro needs to expand into in the first place, right?
! CHR: expand-macro @ // { ExpandQuot ?q ?a ?i ?x ?n } -- [ ?a length ?n = ]
CHR: expand-macro @ // { MacroCall ?q A{ ?a } ?p } --
[ ?a ?q with-datastack first :>> ?v ]
|
! This should cause the current MakeEffect to be suspended, infer expansion
{ ?DeferTypeOf ?v ?sig }
! And return here...
{ Eq ?p ?v }
{ Instance ?p ?sig }
    ;

! **** Generics
! TODO: replace with input/output reasoning?
CHR: generic-dispatch-was-folded @ // { GenericDispatch ?w ?d ?a ?i ?o } -- [ ?d ground-value? ] [ ?a ground-value? ] | ;

! TODO: Instead, should probably carry over instance condition into inlined type closure? nope
! also not good
! Mad heuristics here: expand if we have less than a couple of applicable methods?
! TODO: Building the dispatch via XOR here is probably faster, at least for non-hot caches.
! We still could cache the expansion in predicate form, though, or could we?
CHR: expand-single-generic-dispatch @ { Instance ?d A{ ?c } } // { GenericDispatch ?w { ?d } ?a ?i ?o } --
[ ?w single-generic? ]
[ ?w dispatch# :>> ?n ]
[ ?c ?w method-for-class
  [ ?c swap 2array 1array ]
  [ ?c ?w dispatch-method-seq applicable-methods
    dup length 5 > [ drop f ] when
  ] if* :>> ?l ]
[ ?l >list :>> ?m ]
! [ ?w ?m dispatcher-quot :>> ?q ]
! TODO: closed world assumption: invalid on empty remaining method list
|
! { ?DeferTypeOf ?q ?sig }
{ MakeSingleDispatch ?n ?m ?c ?sig }
{ ApplyEffect ?sig ?i ?o }
 ;

! { MakeSingleDispatch ?i ?l ?rho }

CHR: dispatch-done @ // { MakeSingleDispatch __ +nil+ __ ?tau } -- | [ ?tau null ==! ] ;

CHR: dispatch-case @ // { MakeSingleDispatch ?i L{ { ?c ?m } . ?r } ?d ?tau } --
! [ ?c ?i dispatch-decl :>> ?l ]
[ ?c class-not ?d class-and :>> ?e ]
[ ?d ?i dispatch-decl :>> ?l ]
[ ?m 1quotation :>> ?q ]
|
! Lazy version, not working correctly
! { MakeSingleDispatch ?i ?r ?e ?sig }
! ! { WrapClasses ?l f ?sig ?z }
! { MakeXor P{ Effect ?a ?b f {
!                    P{ ?DeferTypeOf ?q ?rho }
!                    P{ ApplyEffect ?rho ?a ?b }
!                } }
!   P{ Effect ?x ?y  f {
!          P{ Ensure ?l ?x }
!          P{ ApplyEffect ?sig ?x ?y }
!      } }
!   ?tau
! } ;
{ ?DeferTypeOf ?q ?rho }
{ MakeSingleDispatch ?i ?r ?e ?sig }
! { WrapClasses ?l f ?sig ?z }
{ MakeXor P{ Effect ?a ?b f {
                   ! P{ ?DeferTypeOf ?q ?rho }
                 P{ Ensure ?l ?a }
                 P{ ApplyEffect ?rho ?a ?b }
               } }
  ?sig
  ?tau
} ;

! { TypeOfWord ?m ?a }
! TODO: make this a declare quot instead of pred?
! Here we prefix the method word type with the excluded cases from the ordered dispatch
! { ComposeType P{ Effect ?b ?b f { P{ Declare ?l ?b } } } ?a ?rho }
! { MakeSingleDispatch ?i ?r ?sig }
! { MakeXor ?rho ?sig ?d }
! { CheckXor ?m ?d ?tau } ;
CHR: invalid-eq-literals @ { Eq A{ ?a } A{ ?b } } // -- | [ "substituted into eq lits!" throw ] ;

CHR: known-slot-num @ { Eq ?n A{ ?a } } // { Slot ?o ?n ?v } -- |
{ Slot ?o ?a ?v } ;

CHR: known-length-val @ { Eq ?n A{ ?v } } // { Length ?a M{ ?n } } -- |
{ Length ?a ?v } ;

! CHR: known-slot-loc-num @ { Eq ?n A{ ?m } } // { SlotLoc ?x ?o ?n } -- |
! { SlotLoc ?x ?o ?m } ;

CHR: known-instance @ { Eq M{ ?c } A{ ?d } } // { Instance ?x M{ ?c } } --
| { Instance ?x ?d } ;

CHR: known-declared-instance @ { Eq ?c A{ ?d } } // { DeclaredInstance ?x ?c } --
| { DeclaredInstance ?x ?d } ;

CHR: known-not-instance @ { Eq ?c A{ ?d } } // { DeclaredNotInstance ?x ?c } --
| { DeclaredNotInstance ?x ?d } ;

CHR: known-tag-num @ { Eq ?n A{ ?v } } // { Tag ?c ?n } -- |
{ Tag ?c ?v } ;

! UNION: replacable-pred expr-pred fold-pred ;
CHR: known-expr-val @ { Eq ?n A{ ?v } } // AS: ?p <={ expr-pred } -- [ ?n ?p vars in? ]
[ ?p Eq? not ]
! [ ?p NotSame? not ] ! definitely not a HACK!
| [ ?p { { ?n ?v } } lift* ] ;

CHR: known-generic-input/output @ { Eq ?n A{ ?v } } // { GenericDispatch ?w ?d ?a ?i ?o } -- [ ?n ?a in? ?n ?d in? or ] |
[| |
 ?a { { ?n ?v } } lift* :> new-outs
 ?d { { ?n W{ ?v } } } lift* :> new-dispatcher
 P{ GenericDispatch ?w new-dispatcher new-outs ?i ?o } ] ;

! CHR: known-generic-dispatch-class @ { Instance ?x ?tau } // { GenericDispatch ?w ?d ?a ?i ?o } -- [ ?x ?d in? ] |
! [| | ?d { { ?x ?tau } } lift* :> new-dispatcher
!  P{ GenericDispatch ?w new-dispatcher ?a ?i ?o } ] ;

! *** Slot conversion
! PREDICATE: class-with-slots < class all-slots empty? not ;
GENERIC: get-slot-spec ( class n -- ? )

CHR: convert-to-named-slot @ { Instance ?o Is( class ?tau ) } // { Slot ?o Is( union{ string integer } ?n ) ?v } --
[ ?tau ?n get-slot-spec :>> ?s ]
! [ ?tau tuple-class? ]
! [ ?tau all-slots [ offset>> ?n = ] find nip :>> ?s ] ! [ ?s name>> :>> ?m ]
[ ?s class>> :>> ?rho ]
|
! { Slot ?o ?m ?v }
{ Slot ?o ?s ?v }
{ DeclaredInstance ?v ?rho } ;

M: string get-slot-spec swap all-slots [ name>> = ] with find nip ;
M: integer get-slot-spec swap all-slots [ offset>> = ] with find nip ;

! CHR: eql-obj-slot-is-same-loc @ { SlotLoc ?x ?o ?n } <={ Eql ?n ?m } // { SlotLoc ?y ?o ?m } -- |
! [ ?y ?x ==! ] ;

CHR: eql-obj-slot-is-same-slot @ { Slot ?o ?n ?x } <={ Eql ?n ?m } // { Slot ?o ?m ?y } -- |
[ ?y ?x ==! ] ;

! CHR: same-obj-slot-is-same-loc @ { SlotLoc ?x ?o ?n } // { SlotLoc ?y ?o ?n } -- |
! [ ?y ?x ==! ] ;
CHR: same-obj-slot-is-same-slot @ { Slot ?o ?n ?x } // { Slot ?o ?n ?y } -- |
[ ?y ?x ==! ] ;

! TODO invalidate undefined slot stuff here?
! CHR: slot-loc-known-slot-spec @ { Instance ?o Is( class-with-slots ?tau ) } // { SlotLoc ?x ?o Is( union{ string integer } ?n  ) } --
! [ ?tau ?n get-slot-spec :>> ?s ] [ ?s class>> :>> ?rho ] |
! { SlotLoc ?x ?o ?s } ;


IMPORT: chr-intra-effect-maps

CHR: known-boa-spec @ { Eq ?c A{ ?v } } // AS: ?p <={ Boa ?c ?i ?o } -- |
[ ?p clone ?v >>spec ] ;

! *** Boa handling
! NOTE: This is a crucial point regarding re-definitions if we consider incremental operation
CHR: normalize-tuple-boa @ // { Boa A{ ?v } ?i ?o } --
[ ?v tuple-layout :>> ?c ] |
{ TupleBoa ?c ?i ?o } ;

! NOTE: Completely ignoring the hierarchy here
! NOTE: destructive
CHR: tuple-boa-decl @ // { TupleBoa A{ ?c } ?a L{ ?o . ?b } } --
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
     P{ InitSlot ov iv spec ?b } preds push
     spec class>> :> c
     P{ Instance iv c } preds push
 ] each-index
 in-vars <reversed> >list ?rho lappend :> sin
 P{ Instance ov ?tau } preds push
 L{ ov . ?rho  } :> sout
 [ { ?a L{ ?o . ?b } } { sin sout } ==! ] preds push
 preds <reversed> >array
] ;

CHR: init-slot @ // { InitSlot ?o ?i ?s ?b } -- |
! { SlotLoc ?x ?o ?s }
{ Slot ?o ?s ?x }
{ PushLoc ?x ?b L{ ?i } ?b f } ;

! CHR: init-default-element-slot-loc @ { LocalAllocation ?r ?a } { Instance ?a Is( classoid ?tau ) } { Length ?a A{ ?n } } // { Element ?a ?v } --
CHR: init-default-element-slot @ { LocalAllocation ?r ?a } { Instance ?a Is( classoid ?tau ) } { Length ?a A{ ?n } } // { Element ?a ?v } --
[ ?tau array-like class<= ]
! [ ?n 0 > ] [ ?n 1 - 2 + :>> ?u ] | { Le 2 ?m } { Le ?m ?u } { SlotLoc ?x ?a ?m } { PushLoc ?x ?r L{ ?v } ?r t } ;
[ ?n 0 > ] [ ?n 1 - 2 + :>> ?u ] | { Le 2 ?m } { Le ?m ?u } { Slot ?a ?m ?x } { PushLoc ?x ?r L{ ?v } ?r t } ;

GENERIC: read-only-slot? ( class n -- ? )
M: string read-only-slot? swap all-slots [ name>> = ] with find nip
    read-only>> ;
M: integer read-only-slot? swap all-slots [ offset>> = ] with find nip
    dup [ read-only>> ] when ;

! NOTE: there can be multiple ops on the read-only slot, so we have to convert all of them.
! Relying on the SlotLoc not being collected because it can not be live if there is no loc-op
! left marking it live.  Could also change the class of the slotloc predicate and not collect it?
! CHR: convert-read-only-slot-access @ { Instance ?o Is( class ?tau ) }
! { SlotLoc ?x ?o Is( slot-spec ?s ) } //
! <={ LocOp ?x ?a L{ ?v } ?b . __ } -- [ ?s read-only>> ] [ ?s name>> :>> ?n ] |
! [ ?a ?b ==! ] { Slot ?o ?n ?v } ;
CHR: collapse-read-only-slot-access @ { Slot ?o Is( slot-spec ?s ) ?x } //
<={ LocOp ?x ?a L{ ?v } ?b . __ } -- [ ?s read-only>> ] [ ?s name>> :>> ?n ] |
[ ?a ?b ==! ] ;

! NOTE: this is kind of the sledge-hammer version... converting a literal to slot predicates only... might be nicer to only do that to the slots in question...
! CHR: unboa-literal-allocation @ { LocalAllocation ?u ?o } { Instance ?o Is( not{ ro-tuple-class } ?tau ) } { SlotLoc ?x ?o __ } <={ LocOp ?x ?a . __ } // { Eq ?o A{ ?l } } --
CHR: unboa-literal-allocation @ { LocalAllocation ?u ?o } { Instance ?o Is( not{ ro-tuple-class } ?tau ) } { Slot ?o __ ?x } <={ LocOp ?x ?a . __ } // { Eq ?o A{ ?l } } --
[ ?a ?u same-state? ] |
[ ?tau all-slots
  [| slot-spec |
   ?l slot-spec offset>> slot :> slot-lit
   ! slot-spec class>> :> slot-class
   slot-lit class-of :> slot-class
   slot-spec name>> utermvar :> slot-var
   P{ Eq slot-var slot-lit }
   ! NOTE: using the declared class here to make sure any predicates are applied
   ! NOTE2: not doing that, because to be a literal, this would have been ensured already, and
   ! the most specific class needs to be taken from a literal
   ! P{ DeclaredInstance slot-var slot-class }
   P{ Instance slot-var slot-class }
   P{ InitSlot ?o slot-var slot-spec ?a }
   3array
   slot-lit local-alloc-val? [ P{ LocalAllocation ?a slot-var } suffix ] when
  ] map concat
  ?l array-like?
  [
       ?l [| elt i | i 2 + :> elt-num
       "elt" utermvar :> elt-var
       elt class-of :> elt-class
       P{ Eq elt-var elt }
       P{ Instance elt-var elt-class }
       P{ InitSlot ?o elt-var elt-num ?a }
       3array
       elt local-alloc-val? [ P{ LocalAllocation ?a elt-var } suffix ] when
      ] map-index
      append
  ] when
] ;

! Cloning: Structure must be the same before and after.  RO-Slots must be the same before and after. Locally allocated
! PushLocs must be the same value after.  Alternatively, consider this a read-access on the original slot?
! CHR: copy-cloned-ro-slots @ { Cloned ?y ?x } { Slot ?x Is( slot-spec ?s ) ?v } // -- [ ?s read-only>>  ] | { Slot ?y ?s ?v } ;
CHR: copy-cloned-ro-slots-reverse @ { Cloned ?x ?y __ } { Slot ?x Is( slot-spec ?s ) ?v } // -- [ ?s read-only>>  ] | { Slot ?y ?s ?v } ;

! *** State and Locations via FMC semantics

: >states ( row -- seq ) dup array? [ 1array ] unless [ lastcdr ] map ;

CHR: unique-loc-pop @ { LocPop ?x ?a ?s ?b ?m ?u } // { LocPop ?x ?a ?s ?b ?m ?v } --
[ ?u ?v [ >states members ] same? ] | ;

! *** Beta
CHR: resolve-loc-op @ // <={ LocOp __ ?a L{ } ?b __ . __ } -- |
[ ?a ?b ==! ] ;

! ! Also TODO: translate that stuff into Nth...
! : valid-slot? ( length slot-num -- ? )
!     [ 1 - ] dip 2 - swap 0 swap between? ;

! : pseudo-literal-eq ( lhs rhs -- pred )
!     dup ground-value? [ <wrapper> ] when
!     2dup [ term-var? ] both? [ ==! ] [ Instance boa ] if ;

! TODO: Modifying literals is probably too flimsy.  Would be safer and share mode code paths to deconstruct
! as if they were local allocations.  The exception are read-only tuples, which will be reconstructed as soon as possible.
! NOTE: literals are always local allocations, no? Yes, but sequencing will break if we don't keep track of the allocation state
! TODO: unify both below rules, do sanity checks elsewhere (if at all)
! NOTE: it seems that sequencing goes haywire if we actually equalize the states here?
! CHR: literal-apply-slot-loc-pop-request @ { LocalAllocation ?u ?o } { Eq ?o Is( not{ integer } ?a ) } { SlotLoc ?x ?o A{ ?n } }
! { LocPop ?x ?r L{ ?v } ?s t ?b } // -- [ ?u ?b same-state? ] |
! [ ?a ?n dup slot-spec? [ offset>> ] when slot
!   [ ?v swap pseudo-literal-eq 1array ] keep
!   local-alloc-val? [ P{ LocalAllocation ?s ?v } suffix ] when
!   ! ?r ?s ==! suffix
! ] ;

! CHR: perform-literal-read-slot-update @ { LocalAllocation ?u ?o } { SlotLoc ?x ?o A{ ?n } } { Eq ?o Is( not{ integer } ?l ) } //
! { LocPop ?x ?a L{ ?v } ?b t ?d } { PushLoc ?x ?b L{ ?v } ?c t } -- [ ?u ?a same-state? ] [ ?d >states first ?u same-state? ] |
! [ ?a ?c ==! ] ;

! ! NOTE: creating a copy here because otherwise the type inference would actually modify allocations inside the analyzed quotation.
! ! This also means reducing the equality from eq to eql.  Proper identity propagation should be performed via the variables.
! CHR: perform-literal-write-slot-update @ { LocalAllocation ?u ?o } { SlotLoc ?x ?o A{ ?n } } { Eq ?w A{ ?k } } //
! { Eq ?o Is( not{ integer } ?l ) } { LocPop ?x ?a L{ ?v } ?b t ?d } { PushLoc ?x ?b L{ ?w } ?c t } --
! [ ?u ?a same-state? ] [ ?d >states first ?u same-state? ] |
! [ ?k ?l clone [ ?n set-slot ] keep ?o swap Eql boa ]
! [ ?a ?c ==! ] ;

! ! TODO: extend this to local allocations.  In fact, maybe don't use the element mechanism, rather use a cyclic
! ! loc-push like InitSlot, and set up the "value-info" of the slot location so that a local pushloc can be
! ! resolved based on the slot number properties.  The element mechanism would be useful with the nth set-nth location
! ! abstraction on the generic level.
! ! NOTE: this is a special case, since we are actually swapping the reduction order here locally
! ! The intuition is that theses local pushes are always preceeded by a loc-pop on that exact same location
! ! TODO: could still be the case that the allocation needs to be "transported" if the preceding loc-pop was transporting...
! CHR: literal-resolve-numeric-push-loc-request @ { LocalAllocation ?u ?o } { SlotLoc ?x ?o Is( integer ?n ) } //
! { Eq ?o Is( not{ fixnum } ?a ) } <={ PushLoc ?x ?r L{ ?v } ?s t } --
! [ ?u ?r same-state? ]
! [ ?v ?a clone ?n [ set-slot ] keepd :>> ?b ] |
! [ ?r ?s ==! ] { Eq ?o ?b } ;

! Re-create initializer semantics
! CHR: compact-local-writeback @ { LocalAllocation ?u ?o } { SlotLoc ?x ?o __ } { PushLoc M{ ?x } ?a __ ?b t } // -- [ ?a ?b == not ] |
CHR: compact-local-writeback @ { LocalAllocation ?u ?o } { Slot ?o __ ?x } { PushLoc M{ ?x } ?a __ ?b t } // -- [ ?a ?b == not ] |
[ ?a ?b ==! ] ;

! NOTE: keeping any circularities here because that represents a slot read/writeback.  Note that two circularities with different
! items represent parallel reads on the same object, and can be reduced
CHR: beta-reduce-loc-push-pop @ //
{ PushLoc ?l ?a L{ ?x . ?v } ?b ?m } { LocPop ?l ?c L{ ?y . ?w } ?d ?n ?u } --
[ ?u >states first ?b same-state? ] [ ?a ?d same-state? L{ ?x . ?v } L{ ?y . ?w } == and not ] |
[ ?x ?y ==! ]
{ PushLoc ?l ?a ?v ?b ?m } { LocPop ?l ?c ?w ?d ?n ?u } ;

! **** Redex-searching
CHR: independent-loc-op-extends-beta-chain @ <={ LocOp ?y ?a __ ?b ?m . __ } // { LocPop ?x ?c ?s ?d ?n ?u } --
! TODO: would only need to check the first two chain links right now because the maximum loop length is 2
[ ?m [ ?x ?y == not ] [ ?x R? ] if ] [ ?u >states :>> ?v first ?b same-state? ] [ ?a lastcdr ?b lastcdr 2array ?v subseq? not ]
[ ?v ?a prefix :>> ?w ]
|
{ LocPop ?x ?c ?s ?d ?n ?w } ;

! **** Resolve clone slot access
! Approach: if there is a locpop on a cloned object's slot, duplicate the content as initial pushloc.
CHR: copy-cloned-slot-access @ { Cloned ?x ?y ?a } { Slot ?y ?i ?v } { PushLoc ?v __ ?r ?a __ } { Slot ?x ?i ?w } { LocPop ?w __ ?s __ __ ?b } // --
[ ?b >states first ?a same-state? ] | { PushLoc ?w ?a ?r ?a t } ;

! **** Sanity check
! NOTE: a rule like this should only be needed if parallel composition of read accesses is done
! CHR: same-loc-pop-same-loc-same-state @ { LocPop ?x ?a ?s __ __ __ } { LocPop ?x ?a ?r __ __ __ } // -- | [ ?s ?r ==! ] ;

! TODO: Move those checks to the end?
! CHR: duplicate-loc-op-in @ // AS: ?p <={ LocOp ?x ?a __ __ __ . __ } AS: ?q <={ LocOp ?x ?b __ __ __ . __ } -- [ ?a ?b same-state? ] |
! [ { ?p ?q "duplicate loc op in" } throw ] ;

! CHR: duplicate-loc-op-out @ // AS: ?p <={ LocOp ?x __ __ ?a __ . __ } AS: ?q <={ LocOp ?x __ ?b __ . __ } -- [ ?a ?b same-state? ] |
! [ { ?p ?q "duplicate loc op out" } throw ] ;


! **** Special cases

! NOTE: While the reduction with the local allocation predicate as implicit push-loc may only start from the head,
! the fact that the allocation is local does not change anymore, so we can localize all loc-ops, not only the first?
! CHR: slot-loc-op-known-local @ { LocalAllocation __ ?o } { SlotLoc ?x ?o __ } // AS: ?p <={ LocOp M{ ?x } ?b ?s ?c f . __ } --
CHR: slot-loc-op-known-local @ { LocalAllocation __ ?o } { Slot ?o __ ?x } // AS: ?p <={ LocOp M{ ?x } ?b ?s ?c f . __ } --
| [ ?p clone t >>local? ] ;

CHR: slot-loc-op-known-local-cloned @ { Cloned ?o __ __ } { Slot ?o __ ?x } // AS: ?p <={ LocOp M{ ?x } __ __ __ f . __ } --
| [ ?p clone t >>local? ] ;

! ! TODO: put the length check somewhere else, as it is independent from the actual loc op!
! ! TODO: extend to byte-arrays and strings
! ! NOTE: setting an arbitrary limit here to prevent explosion during compilation...
! CHR: literalize-local-array @ { Instance ?o array } //
! { LocalAllocation ?o } { Element ?o ?x } { PushLoc ?x f L{ ?y } __ } { Eq ?y A{ ?v } }
! { Length ?o ?l } { Eq ?l Is( fixnum ?m ) } -- [ ?m 16 <= ] | [ ?o ?m ?v <array> Eq boa ] ;

! NOTE: do we need transitive eq rules?  Or do they break implications...
! CHR: same-obj-slot-is-same-loc @ { SlotLoc ?x ?o ?n } { Eq ?n ?a } { Eq ?m ?a } // { SlotLoc ?y ?o ?m } -- |

! **** Input-output proper values
! NOTE: we are relying on the cdrs of the stacks to encode states for sequencing.
! After execution of the effect, the stacks will be unified.  However, we assume all effects
! will be executed.  That means the stack elements can be assumed to be
! unified in the end.  Thus, we can unify them in advance.
! NOTE: this could potentially result in an endless loop when constructing
! recursive structures?
! TODO: maybe extend this to balancing!
CHR: unify-loc-op-io-vals @ // AS: ?p <={ LocOp ?l L{ ?x . ?a } ?s L{ ?y . ?b } ?m . __ } -- |
[ ?x ?y ==! ] [ ?p clone ?a >>before ?b >>after ] ;

CHR: balance-loc-op-produce @ // AS: ?p <={ LocOp ?l L{ ?x . ?a } __ M{ ?b } ?m . __ } -- |
[ ?b L{ ?x . ?c } ==! ] [ ?p clone ?a >>before ?c >>after ] ;

CHR: balance-loc-op-consume @ // AS: ?p <={ LocOp ?l M{ ?b } __ L{ ?y . ?c } ?m . __ } -- |
[ ?b L{ ?y . ?a } ==! ] [ ?p clone ?a >>before ?c >>after ] ;

! *** Locals scope expansion

! Propagate liveness of parameter if it is one connecting predicates together
! CHR: add-dangling-pred-implication-join @ AS: ?p <={ val-pred } AS: ?q <={ val-pred } // --
! CHR: add-dangling-pred-implication-join @ AS: ?p <={ expr-pred } AS: ?q <={ expr-pred } // --
! [ ?p vars :>> ?a length 1 > ]
! [ ?q vars :>> ?b length 1 > ]
! [ ?a ?b intersect :>> ?c null? not ]
! [ ?a ?b union ?c diff :>> ?x null? not ] |
! { ImpliesParam ?x ?c } ;

! Pivot literal output stuff
! TODO: This special-case-repairs the fact that we reversed the predicates for - and / instead of defining them in-order...
CHR: pivot-output-literal-product @ { MakeEffect ?a ?b __ __ __ } // { Prod ?y ?x A{ ?m } } -- [ ?x ?b vars in? ] [ ?x ?a vars in? not ]
[ 1 ?m / :>> ?k ] | { Prod ?x ?y ?k } ;
CHR: pivot-output-literal-sum @ { MakeEffect ?a ?b __ __ __ } // { Sum ?y ?x A{ ?m } } -- [ ?x ?b vars in? ] [ ?x ?a vars in? not ]
[ 0 ?m - :>> ?k ] | { Sum ?x ?y ?k } ;

    ;
