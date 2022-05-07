USING: accessors chr chr.factor chr.factor.terms chr.parser chr.state
classes.algebra kernel sequences sets terms ;

IN: chr.factor.effects

! * Effect types

TUPLE: Effect < chr-pred word parms in out constraints ;
TUPLE: InferEffect < chr-pred word parms in out constraints ;
! TUPLE: InferDataEffect < InferEffect ;

CHRAT: chr-effects {  }

! If we turn out to infer the same thing, combine.
CHR: unique-inference-marker @ AS: ?x <={ InferEffect ?w ?c ?a ?b ?l } // AS: ?y <={ InferEffect ?w ?c ?a ?b ?l } -- [ ?x ?y class= ] | [ "srsly?" throw ] ;
CHR: combine-inference-marker @ // { InferEffect ?w ?c ?a ?b ?l } { InferEffect ?w ?c ?a ?b ?k } -- [ ?l ?k union :>> ?m ] | [ "öhm..." throw ]
{ InferEffect ?w ?c ?a ?b ?m } ;


! : tags-contradict? ( set1 set2 -- ? )
!     [ neg swap in? ] with any? ;

! CHR: impossible-effect @ // { Effect __ ?c __ __ __ } -- [ ?c dup tags-contradict? ] | ;
CHR: impossible-effect @ False{ ?c } // { Effect __ ?c __ __ __ } -- | ;

CHR: redundant-effect @ { Effect ?w ?c ?a ?b ?l } // { Effect ?w ?c ?a ?b ?l } -- | ;

! Expand Effect Conjunctions

! Approach: fix-point iteration on the set of constraints?
CHR: subsuming-effect @ { Effect ?w ?c ?a ?b ?l } // { Effect ?w ?d ?x ?y ?k } -- [ ?c ?d set= ] [ ?k ?l subset? ] |
! NOTE: This could be problematic regarding recursion? maybe do, because of effect matching?
[ { ?a ?b } { ?x ?y } ==! ]
;


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

! CHR: collect-effect-regular-pred @ // AS: ?e <={ InferEffect __ __ __ __ ?l } AS: ?k <={ type-pred } --
CHR: collect-effect-regular-pred @ AS: ?k <={ type-pred } // AS: ?e <={ InferEffect __ __ __ __ ?l } --
[ ?k ?l in? not ] [ ?e bound-vars :>> ?v ]
[ ?k free-vars ?v subset? ] |
[ ?e [ ?k suffix ] change-constraints ] ;

! CHR: collect-nested-effect @ AS: ?e <={ InferEffect ?q ?m __ __ ?l } // AS: ?k P{ Effect ?w ?n __ __ __ } --
! Collect nested effects under the same condition
! CHR: collect-nested-effect @ AS: ?k P{ Effect ?w ?n __ __ __ } // AS: ?e <={ InferEffect ?q ?n __ __ ?l } --
! [ ?w ?q == not ]
! [ ?k ?l in? not ] [ ?e vars :>> ?v ] [ ?w ?v in? ] |
! [ ?e [ ?k suffix ] change-constraints ] ;
! [ ?k ?e constraints>> push f ] ;


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
