USING: accessors arrays assocs chr chr.comparisons chr.factor chr.factor.terms
chr.parser chr.state combinators.short-circuit kernel lists namespaces sequences
sets terms ;

IN: chr.factor.effects

! * Effect types

! TUPLE: Effect < chr-pred word parms in out constraints ;
TUPLE: Effect < chr-pred word parms in out constraints ;
TUPLE: InferEffect < chr-pred word parms in out constraints ;
TUPLE: ApplyEffect < chr-pred in out effect ;
! TUPLE: InferDataEffect < InferEffect ;

CHRAT: chr-effects {  }


! ** Call sites

! CHR: call-effect @ // Is{ ?b { call ?a } } -- |
! Is{ L{ ?p . ?rho } ?a }
! Is{ ?b ?sig }
! ! Is{ ?b ?rho }
! { Effect ?p f ?rho ?sig f }
!     ;
! CHR: call-effect @ // Is{ ?b { call ?a } } -- |
! Is{ L{ ?p . ?rho } ?a }
! Is{ ?b ?sig }
! ! Is{ ?b ?rho }
! { Effect ?p f ?rho ?sig f }
!     ;

! This creates a connection between an effect predicate and the variables in the calling context
! CHR: call-effect @ Is{ ?b { call L{ ?p . ?a } } } // -- |
! ! Is{ L{ ?p . ?rho } ?a }
! Is{ ?rho ?a }
! Is{ ?b ?sig }
! { Effect ?p f ?rho ?sig f }
!     ;


! If we turn out to infer the same thing, combine.
! CHR: unique-inference-marker @ AS: ?x <={ InferEffect ?w ?c ?a ?b ?l } // AS: ?y <={ InferEffect ?w ?c ?a ?b ?l } -- [ ?x ?y class= ] | [ "srsly?" throw ] ;
! CHR: combine-inference-marker @ // { InferEffect ?w ?c ?a ?b ?l } { InferEffect ?w ?c ?a ?b ?k } -- [ ?l ?k union :>> ?m ] | [ "öhm..." throw ]
! { InferEffect ?w ?c ?a ?b ?m } ;


! : tags-contradict? ( set1 set2 -- ? )
!     [ neg swap in? ] with any? ;

! CHR: impossible-effect @ // { Effect __ ?c __ __ __ } -- [ ?c dup tags-contradict? ] | ;
CHR: impossible-effect @ False{ ?c } // { Effect __ ?c __ __ __ } -- | ;

CHR: redundant-effect @ { Effect ?w ?c ?a ?b ?l } // { Effect ?w ?c ?a ?b ?l } -- | ;

! NOTE: this depends on the effect outputs never being the variables that are inside the effects...
! At least Making dup'd variables equal breaks this pretty badly
! CHR: same-effect-vars @ { Effect ?q __ ?a ?b __ } { Effect ?q __ ?c ?d __ } // -- | [ { ?a ?b } { ?c ?d } ==! ] ;
! [ { ?a ?b } { ?c ?d } ==! ] ;

: instantiate-effect ( Effect -- Effect )
    dup bound-vars fresh-with ;

: in-context? ( current-ctx susp-ctx -- ? )
    over [
        =
    ] [ 2drop t ] if ;

! NOTE: Expensive!
: get-context-bindings ( -- res )
    V{ } clone
    store get
    current-context get
    '[ nip
        _ over { [ ctx>> in-context? ] [ constraint>> Is? ] } 1&&
        [ constraint>> [ var>> ] [ src>> ] bi [ ?ground-value ] bi@
          ! 2dup [ term-var? ] both?
          over term-var?
          [ 2array suffix! ] [ 2drop ] if ]
        [ drop ] if
     ] assoc-each ;

: ground-value-in-context ( term -- term )
    f lift get-context-bindings lift ;

: solve-in-context ( eq1 eq2 -- res )
    [ get-context-bindings ] 2dip
    2array 1array [ solve-next ] no-var-restrictions ;

CHR: do-apply-effect-on @ // { ApplyEffect ?a ?b ?e } -- |
[| | ?e instantiate-effect [ in>> ] [ out>> ] [ constraints>> ]
 tri :> ( in out body )
 ! { in out } { ?a ?b } [ solve-eq ] no-var-restrictions drop
 { in out } { ?a ?b } solve-in-context drop
 {
     Is{ in ?a }
     Is{ ?b out }
     body
 }
] ;

! FIXING: Completely rebuild with fresh vars!
! ! CHR: same-effect-vars @ { Effect ?q __ ?a ?b __ } // AS: ?e P{ Effect ?q __ ?c ?d ?l } -- |
! CHR: same-effect-vars @ { Effect ?q __ ?a ?b __ } // AS: ?e P{ Effect ?q __ __ __ __ } -- |
! { ApplyEffect ?a ?b ?e } ;
! ! [
! !     ! Make sure we don't create a recursive effect
! !     { ?a ?b } { ?c ?d } solve-eq drop f ]
! ! [| | ?e instantiate-effect [ in>> ] [ out>> ] [ constraints>> ]
! !   tri :> ( in out body )
! !   body { in out } { ?a ?b } break [ solve-eq ] no-var-restrictions lift
! ! ] ;

! Approach: fix-point iteration on the set of constraints?
! CHR: subsuming-effect-same-ctx @ { C ?c P{ Effect ?w __ ?a ?b ?l } } // { C ?c P{ Effect ?w __ ?x ?y ?k } } -- [ ?k ?l subset? ] |
CHR: subsuming-effect @ P{ Effect ?w __ ?a ?b ?l } // P{ Effect ?w __ ?a ?b ?k } -- [ ?k ?l subset? ] |
! NOTE: This could be problematic regarding recursion? maybe do, because of effect matching?
! [ { ?a ?b } { ?x ?y } ==! ]
    ;

! ! NOTE: this SHOULD _not_ cause effects to be re-applied, only to be re-inferred!
CHR: rebuild-effect-conjunction @ { Effect ?q __ ?a ?b ?k } // AS: ?e P{ Effect ?q __ ?x ?y ?l } -- |
[ ?e instantiate-effect
  [ [ in>> ] [ out>> ] bi 2array { ?a ?b } ==! ]
  [ constraints>> ] bi 2array
] ;

! ! NOTE: this SHOULD _not_ cause effects to be re-applied, only to be re-inferred!
! ! NOTE: version without re-instantiating
! CHR: rebuild-effect-conjunction @ { Effect ?q __ ?a ?b ?k } // AS: ?e P{ Effect ?q __ ?x ?y ?l } -- |
! [ ?e
!   [ [ in>> ] [ out>> ] bi 2array { ?a ?b } ==! ]
!   [ constraints>> ] bi ?k diff 2array
! ] ;

! Expand Effect Conjunctions

! CHR: make-dispatch-effect @ // P{ Effect ?w ?c ?a ?b ?k } P{ Effect ?w ?d ?x ?y ?l } -- |
! [| |
!  { ?x ?y } { ?a ?b } unify :> mapping
!  ?l mapping lift :> l
!  ?k l intersect :> common
!  ?k common diff :> only-k
!  l common diff :> only-l
!  common
!  Cond{ { ?c only-k } { ?d only-l } } suffix :> body
!  ! P{ Effect ?w f ?a ?b body }
!  P{ InferEffect ?w f ?a ?b body }
! ]
! { InferDone ?w }
!     ;
! }

! ** Contract Effects

UNION: refine-pred type-pred comp-pred ;


! CHR: collect-effect-regular-pred @ AS: ?k <={ type-pred } // AS: ?e <={ Effect __ __ __ __ ?l } --
! CHR: collect-effect-regular-pred @ // AS: ?k <={ type-pred } AS: ?e <={ Effect __ ?c __ __ ?l } --
! CHR: collect-effect-regular-pred @ // AS: ?k <={ refine-pred } AS: ?e <={ Effect __ ?c __ __ ?l } --
! CHR: collect-effect-regular-pred @ { C ?c AS: ?k <={ refine-pred } } // { C ?c AS: ?e <={ Effect __ __ __ __ ?l } } --
! CHR: collect-effect-regular-pred @ // { C ?d AS: ?k <={ refine-pred } } { C ?c AS: ?e <={ Effect __ __ __ __ ?l } } --
! CHR: collect-effect-regular-pred @ // AS: ?k <={ refine-pred } AS: ?e <={ Effect __ __ __ __ ?l } --
! ! [ ?c not ]
! ! Either we have the same condition, or we import a more special predicate
! ! [ ?c ?d and [ ?c ?d = ] [ ?c not ] if ]
! [ ?k ?l in? not ] [ ?e bound-vars :>> ?v ]
! [ ?k free-vars ?v subset? ] |
! ! [ ?e [ ?k ?d [ swap C boa ] when* suffix ] change-constraints ?c swap C boa ] ;
! [ ?e [ ?k suffix ] change-constraints ] ;

CHR: collect-effect-top-pred @ // { C ?d AS: ?k <={ refine-pred } } { C ?c AS: ?e <={ Effect __ __ __ __ ?l } } --
[ ?c not ]
! Either we have the same condition, or we import a more special predicate
[ ?c ?d and [ ?c ?d = ] [ ?c not ] if ]
[ ?k ?l in? not ] [ ?e bound-vars :>> ?v ]
[ ?k free-vars ?v subset? ] |
[ ?e [ ?k ?d [ swap C boa ] when* suffix ] change-constraints ?c swap C boa ] ;

CHR: infer-existential-effect-var @ { C ?d AS: ?k Is{ ?y ?x } } // { C ?c AS: ?e P{ Effect __ __ ?a ?b ?l } } --
[ ?c not ]
[ ?c ?d and [ ?c ?d = ] [ ?c not ] if ]
[ ?k ?l in? not ] [ ?e bound-vars :>> ?v ]
[ ?y free-vars ?v subset? ]
[ ?x free-vars :>> ?xs ]
[ ?xs ?v subset? not ]
[ ?a vars ?b vars union :>> ?p ]
|
[ ?e [ ?xs union ?p diff ] change-parms ] ;



CHR: collect-nested-effect-in-top-effect @ // { C ?d AS: ?k P{ Effect ?x __ __ __ __  } } { C ?c AS: ?e <={ Effect __ __ __ __ ?l } } --
[ ?c not ]
[ ?c ?d and [ ?c ?d = ] [ ?c not ] if ]
[ ?k ?l in? not ] [ ?e bound-vars :>> ?v ]
[ ?x ?v in? ] |
[ ?e [ ?k ?d [ swap C boa ] when* suffix ] change-constraints ?c swap C boa ] ;

! CHR: assume-sub-scope-effect @ { C ?d AS: ?k <={ refine-pred } } { C ?c AS: ?e <={ Effect __ __ __ __ ?l } } // --
! [ ?c not ]
! [ ?d ]
! [ ?k ?l in? not ] [ ?e bound-vars :>> ?v ]
! [ ?k free-vars ?v subset? ] |
! [ ?e [ ?k suffix ] change-constraints ?d swap C boa ] ;

! ! CHR: collect-nested-effect @ AS: ?e <={ InferEffect ?q ?m __ __ ?l } // AS: ?k P{ Effect ?w ?n __ __ __ } --
! ! Collect nested effects under the same condition
! ! CHR: collect-nested-effect @ AS: ?k P{ Effect ?w ?n __ __ __ } // AS: ?e <={ InferEffect ?q ?n __ __ ?l } --
! CHR: collect-nested-effect @ // AS: ?k P{ Effect ?w ?n __ __ __ } AS: ?e <={ Effect ?q ?n __ __ ?l } --
! [ ?w ?q == not ]
! [ ?k ?l in? not ] [ ?e vars :>> ?v ] [ ?w ?v in? ] |
! [ ?e [ ?k suffix ] change-constraints ] ;
! ! [ ?k ?e constraints>> push f ] ;


! CHR: finish-infer-effect-on-demand @ // { InferDone ?n } { InferEffect ?n ?c ?a ?b ?k } --
! | [| |
!    ?k >array :> body
!    ! ?c { ?a ?b ?k } vars in? [ ?c ] [ f ] if :> c
!    P{ Effect ?n ?c ?a ?b body }
!    dup bound-vars :> vars
!    P{ Marked ?n vars }
!    swap 2array
!   ] ;


! CHR: finish-infer-effect-simple @ // { InferEffect ?n ?c ?a ?b ?k } -- |
! { Effect ?n ?c ?a ?b ?k } ;

;
