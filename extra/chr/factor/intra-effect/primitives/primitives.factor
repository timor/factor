USING: arrays chr.factor chr.parser chr.state classes.algebra kernel lists
locals.backend math math.private sequences sets terms types.util ;

IN: chr.factor.intra-effect.primitives

! * Primitive Expansions


CHRAT: chr-factor-prim { }

! *** Math Prim Conversions
! Instances have already been defined at this point
CHR: prim-call-fixnum+fast @ // { PrimCall fixnum+fast L{ ?y ?x . ?a } L{ ?z . ?b } } --
[ ?a ?b ==! ] | { Sum ?z ?x ?y } ;

! FIXME: pred args are stacks now
CHR: prim-call-bitnot @ // { PrimCall ?w { ?x } { ?y } } -- [ ?w { bignum-bitnot fixnum-bitnot } in? ] | { BitNot ?y ?x } ;
CHR: prim-call-fixnum> @ // { PrimCall ?w { ?x } { ?y } } -- [ ?w { fixnum>float fixnum>bignum } in? ] | { Num= ?x ?y } ;
CHR: prim-call-shift @ // { PrimCall fixnum-shift { ?x ?n } { ?y } } -- | { Shift ?y ?x ?n } ;

! ** Composition mode expansions
PREFIX-RULES: { P{ CompMode } }

! *** Cloning

! NOTE: The class pred there has implied directional semantics here, not sure if that is important
CHR: prim-call-clone @ // { PrimCall (clone) L{ ?x . ?a } L{ ?y . ?b } } -- |
[ ?a ?b ==! ] { Eq ?x ?y } { LocalAllocation ?a ?y } { ClassPred ?y ?x class= } ;

! *** Locals
! [| a b | a ] -> [ 2 load-locals -1 get-local 2 drop-locals ]

:: ensure-retain-stack ( n -- list )
    ! "rest" utermvar :> tail
    n [ "pad" utermvar ] replicate >list ;

! L{ ?x . ?a } --> L{ r( ?x ) . ?a } ???

PREDICATE: var-rstack-word < word { load-locals get-local drop-locals } in? ;

CHR: local-prim-type @ { PrimCall Is( var-rstack-word ?w ) L{ ?n . ?a } __ } // -- |
{ Instance ?n fixnum } ;

CHR: do-load-local @ // { PrimCall load-local L{ ?x . ?a } ?b } -- |
{ PushLoc R ?a L{ ?x } ?b t } ;

CHR: do-load-locals @ // { PrimCall load-locals L{ ?n . ?a } ?b } { Eq ?n A{ ?v } } --
[ ?v ensure-retain-stack :>> ?l ] |
[| | ?l ?rho list* :> sout
 ?l ?c list* ?a ==!
 P{ PushLoc R ?c ?l ?b t }
 2array
 ?l [ object Instance boa ] lmap>array append
] ;

CHR: do-drop-locals @ // { PrimCall drop-locals L{ ?n . ?a } ?b } { Eq ?n A{ ?v } } --
[ ?v ensure-retain-stack :>> ?l ] |
[| | ?l ?rho list* :> sin
 P{ LocPop R ?a ?l ?b t ?a }
 ! ?l [ object Instance boa ] lmap>array
 ! swap prefix
] ;

CHR: do-get-local @ // { PrimCall get-local L{ ?n . ?a } L{ ?x . ?b } } { Eq ?n A{ ?v } } --
[ ?v neg ensure-retain-stack L{ ?x } lappend :>> ?l ] |
! [ ?l [ object Instance boa ] lmap>array ] Only needed if we test stuff in isolation
{ LocPop R ?a ?l ?rho t ?a }
{ PushLoc R ?rho ?l ?b t } ;

;
