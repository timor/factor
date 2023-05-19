USING: accessors arrays chr.factor chr.factor.util chr.parser chr.state kernel
lists namespaces sequences sets terms ;

IN: chr.factor.phi

CHRAT: chr-phi { }

! NOTE: While kept for reasoning in straight-line composition,
! we don't allow errors into intersection types
CHR: exclude-error-xor-left @ // { MakeXor P{ Effect __ __ __ ?k } ?sig ?tau } -- [ ?k [ Throws? ] any? ] |
{ MakeXor null ?sig ?tau } ;
CHR: exclude-error-xor-right @ // { MakeXor ?rho P{ Effect __ __ __ ?k } ?tau } -- [ ?k [ Throws? ] any? ] |
{ MakeXor ?rho null ?tau } ;

CHR: fail-on-rhs-xor @ // { MakeXor __ __ ?tau } -- [ ?tau term-var? not ] |
[ ?tau "not term-var in xor" 2array throw f ] ;
CHR: make-null-xor @ // { MakeXor null null ?tau } -- | [ ?tau null ==! ] ;
CHR: make-trivial-xor-left @ // { MakeXor ?rho null ?tau } -- | [ ?rho ?tau ==! ] ;
CHR: make-trivial-xor-right @ // { MakeXor null ?rho ?tau } -- | [ ?rho ?tau ==! ] ;
! ** Phi Reasoning

! Approach: A complete xor can be checked for whether parallel application
! results in disjoint types.  If so, it is indeed an XOR.  If not, generate a union
! type.  The reasoning is as follows: The XOR case is really only interesting
! for disjoint reasoning if we can be sure that applying one set of input/output
! types actually excludes the other alternative.  If we get overlapping types,
! then the intersection is non-empty, and the best we can do is reason with the convex cover.

! The question is how to decide which XOR's to keep.  Going bottom-up, pretty much
! every conditional and/or type test defines two branches.  So for any composition
! of words, the worst-case is a 2^n blow-up in the word length n of branches.
! The reason to keep separate branches of the intersection types in the first
! place is that we want to keep around enough information to exclude stuff during
! composition: If we define a generic function with several methods on disjoint
! data-types, the information loss of actually lumping everything together into
! union classes is comparatively large.  The following cases seem to be
! interesting:

! 1. Depending on disjoint input types, the word defines disjoint output types.
!    This is e.g. a use case where we have separate implementations of say a
!    mapper function.  If we run a mapping operation, we want to be able to
!    transport these dependencies into the Sequence-Of parametric types

! Problem with not having explicit bind/dup operations anymore:
! two effects like ~( x y -- y x )~ and maybe ~( a x -- b x )~ represent different
! kinds of data shuffling (in addition to whatever predicates they have).  For phi
! operations, the general approach is:
! 1. Assume the same input data for stuff
! 2. Run stuff through effect1
! 3. Run stuff through effect2
! 4. Perform union-reasoning on the predicates, collect results.

! Normally, assuming the same input data for stuff means performing unification.
! However there seems to be a problem with that.

! The first effect (~swap~) could also be expressed with explicit bind/dup predicates, e.g.
! ~( x1 y1 -- y2 x2 )~ where ~y2: y1~, and ~x2: x1~.   This means, that an effect
! which does not use explicit var-copying but a single variable for input and
! output var actually "hides" an additional equality constraint between input and
! output.

! Using the "explicit discriminator" approach, we would normally define the member
! s of a relation induced by an equality predicate as parameters of the type.
! I.e. the ~swap~ word would then considered to be a predicate class on a stack
! whose top two elements on output depend on the top two elements on input:


! Forall x, y: (..ρ, x, y) → (..ρ, y, x)


! Approach with implicit phis: if we find that we would get non-unique unifiers
! for the stack effect, then we are hiding implicit equality constraints.  This
! is a sign that two effects are distinct.

CHR: maybe-make-trivial-xor @ // { MakeXor ?rho ?sig ?tau } -- [ ?rho full-type? ] [ ?sig full-type? ] |
[
    ?rho ?sig isomorphic?
    ! TODO: check timing on this!
    ! ?rho ?sig same-effect?
  [ ?tau ?rho ==! ]
  [ ?tau P{ Xor ?rho ?sig } ==! ]
  ! { CheckXor ?rho ?sig ?tau }
  ?
] ;

! Some sanity checks
! CHR: xor-error @ <={ CheckXor } <={ CheckXor } // -- | [ "xor sequencing error" throw ] ;
CHR: phi-error @ <={ PhiSchedule } <={ PhiSchedule } // -- | [ "phi sequencing error" throw ] ;
CHR: current-phi-error @ { CurrentPhi __ } { CurrentPhi __ } // -- | [ "current phi sequencing error" throw ] ;
CHR: make-union-error @ <={ MakeUnion } <={ MakeUnion } // -- | [ "double make-union" throw ] ;

! ** Entry point, xor check request received
! Start Destructuring, trigger schedule

! CHR: also-check-fixpoint @ { CheckXor ?q ?rho ?tau } // -- [ ?rho full-type? ] |
! { CheckFixpoint ?q ?rho } ;


! Returns true if the type contains an unresolved call to an Xor type.  These must "bubble" up
! as quickly as possible.
! TODO: It should not be possible to have these hidden in Effect instance type predicates.
!  The intuition being that they only arise directly from reasoning the innermost defs.
!  Somehow ensure this?

CHR: check-xor-trivial @ // { CheckXor __ ?rho ?tau } --
[ ?rho full-type? ] [ ?rho Effect? ] [ ?rho xor-call? [ "not expecting xor call here" throw ] when t ] |
[ ?rho ?tau ==! ] ;

! If we inferred an effect type to be null, then substitute it with a null-push that will
! cause exclusion of this effect from further Xor reasonings.
! TODO TBR?
CHR: check-xor-null-throws @ // { CheckXor ?q null ?tau } -- [ ?tau term-var? ] |
[ ?tau P{ Effect ?a L{ ?x . ?a } { } { P{ Instance ?x null } } } ==! ] ;

CHR: do-check-xor @ // { CheckXor ?q ?rho ?tau } -- [ ?rho full-type? ] |
[
    "checkxor" [
        P{ DestrucXor ?rho }
        P{ PhiSchedule ?q +nil+ ?tau }
        2array
    ] new-context
]
    ;

! ** Destructuring

PREDICATE: InvalidEffect < Effect preds>> [ Invalid? ] any? ;

CHR: discard-invalid-branch @ // { DestrucXor ?e } -- [ ?e InvalidEffect? ] | ;
CHR: destruc-rebuild-xor @ // { DestrucXor P{ Xor ?a ?b } } -- |
{ DestrucXor ?a } { DestrucXor ?b } ;

CHR: destruc-rebuild-effect @ // { PhiSchedule ?q ?r ?tau } { DestrucXor ?e } -- [ ?e Effect? ] |
{ PhiSchedule ?q L{ ?e . ?r } ?tau } ;

! Triggers actual phi-reasoning
! NOTE: To avoid things like ~[ swap ] when~ to unify the vars,
! the (unknown) vars themselves have to be treated as the types.  So this means that if we meet
! e.g. two effects ~( x y -- y x ) ( a b -- a b )~, we first need to unify the inputs, and then check
! if we can still unify the whole effect.

CHR: try-next-phi @ { CurrentPhi ?a } P{ PhiSchedule __ L{ ?b . ?r } __ } // -- |
[| |
 ?a fresh-effect :> e1
 ?b fresh-effect :> e2
 { P{ MakeUnion e1 e2 ?tau } } ] ;

! Finished force-union schedule
CHR: all-fixpoint-phis-done @ // { PhiSchedule __ +nil+ ?tau } { FixpointMode } { DisjointRoot ?a } -- |
[ ?a Xor? [ ?a "not a straightline-effect" 2array throw ] [ f ] if ]
[ ?tau ?a ==! ] ;

! Finished Schedules
CHR: all-phis-done @ { PhiSchedule __ +nil+ ?tau } // { DisjointRoot ?a } -- |
{ RebuildXor ?a ?tau } ;

:: alpha-equiv-under? ( t1 t2 bound -- subst/f )
    t1 vars t2 vars union bound diff valid-match-vars
    [ t1 t2 solve-eq ] with-variable ;

! *** Rebuild two effects as union
! CHR: check-non-unionable-effect @ { MakeUnion P{ Effect ?a ?b ?x ?l } P{ Effect ?a ?d ?y ?k } ?tau } // -- [ ?tau term-var? ] |
! [
!     ?b ?d ?a vars alpha-equiv-under? not
!     { [ ?tau null ==! ] P{ PhiDone } } f ?
!  ] ;

! Trigger Phi-mode Composition
! This causes the reasoner to assume disjunction instead of conjunction of value predicates.

CHR: make-trivial-union @ { MakeUnion ?a ?b ?tau } // -- [ ?a ?b isomorphic? ] |
[ ?tau ?a ==! ]
{ PhiDone } ;

CHR: try-union-effect @ { MakeUnion ?a ?b ?tau } // -- [ ?tau term-var? ] |
{ PhiMode }
{ ComposeEffect ?a ?b ?tau } ;

! After MakeEffect has finished
CHR: have-union-effect @ // { DisjointRoot ?e } { CurrentPhi ?e } { MakeUnion ?x ?y ?a } { PhiDone } { PhiSchedule ?q L{ ?b . ?r } ?tau } --
[ ?a Effect? ] | { DisjointRoot ?a } { PhiSchedule ?q ?r ?tau } ;

CHR: have-disjoint-effect @ // { CurrentPhi ?e } { MakeUnion ?x ?y null } { PhiDone } -- | ;

CHR: try-next-phi-merge @ { DisjointRoot ?e } { PhiSchedule __ L{ ?b . ?r } __ } // -- | { CurrentPhi ?e } ;

CHR: no-next-phi-merge @ // { PhiSchedule ?q L{ ?b . ?r } ?tau } -- |
{ DisjointRoot ?b } { PhiSchedule ?q ?r ?tau } ;

! *** Rebuild after intersection checking
CHR: rebuild-phi-collect-branch @ { PhiSchedule ?q +nil+ ?tau } // { RebuildXor ?a ?tau } { DisjointRoot ?b } -- |
{ RebuildXor P{ Xor ?b ?a } ?tau } ;

CHR: rebuild-phi-finished @ // { PhiSchedule ?q +nil+ ?tau } { RebuildXor ?a ?tau } -- |
[ ?tau ?a ==! ] ;

! *** Build Fixpoint type
! Either no recursive branches, or unresolved recursive calls
CHR: no-check-fixpoint @ // { CheckFixpoint ?w ?rho } -- [ ?rho ?w recursive-branches? not ] | ;
! CHR: no-check-fixpoint-unresolved @ // { CheckFixpoint ?w ?rho } -- [ ?w ?rho unresolved-recursive? ] | ;
! FIXME: clean up those checks in the body
CHR: do-check-fixpoint @ // { CheckFixpoint ?w ?rho } -- [ ?rho ?w terminating-branches :>> ?l drop t ]
[ ?rho ?w recursive-branches :>> ?k drop t ]
[ ?l >list :>> ?m ]
[ ?k >list :>> ?n ]
|
[ ?l empty? [ "could not prove that effect can terminate" throw ] when f ]
[ "fixtype" [ P{ PhiSchedule ?w ?m ?tau } ] new-context ]
[ "rectype" [ P{ PhiSchedule ?w ?n ?sig } ] new-context ]
{ FixpointTypeOf ?w ?tau }
{ RecursionTypeOf ?w ?sig }
! [| |
!     ?l >list :> fp-phis
!     ?k >list :> rec-phis
!         {
!             ! NOTE: not forcing this to fixpoint mode, because that prevents some useful fixpoints
!             ! from being calculated when done incorrectly.
!             ! 1. Either force fixpoint calculation
!             ! 2. Or deal with Xor Fixpoint types correctly, e.g. by assuming different loop types on
!             ! different loop exits.
!             ! The correct version is probably to infer a recursive version for every base case?
!             ! P{ FixpointMode }
!             P{ PhiSchedule ?w fp-phis ?tau }
!             P{ FixpointTypeOf ?w ?tau }
!         }
!     ] if-empty
!     ?k [ f ] [
!         ! [ ?w swap filter-recursive-call ] map
!         >list :> rec-phis
!         {
!             P{ PhiSchedule ?w rec-phis ?sig }
!             P{ RecursionTypeOf ?w ?sig }
!         }
!     ] if-empty append ]
! ! Generate recursive call type
! ! { ReinferEffect ?sig ?y }
! ! { CheckXor ?w ?y ?z }
! ! ! TODO: maybe make check rule that this one may not contain callrecursives anymore!
! ! { RecursiveCallTypeOf ?w ?z } ;
;

;
