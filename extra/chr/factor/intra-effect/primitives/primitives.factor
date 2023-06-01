USING: arrays chr.factor chr.parser chr.state classes.algebra kernel lists
locals.backend math math.private sequences sets terms types.util ;

IN: chr.factor.intra-effect.primitives

! * Primitive Expansions


CHRAT: chr-factor-prim { }

! *** Math Prim Conversions
! Instances have already been defined at this point
CHR: prim-call-fixnum+fast @ // { PrimCall fixnum+fast L{ ?y ?x . ?a } L{ ?z . ?a } } --
| { Sum ?z ?x ?y } ;

! FIXME: pred args are stacks now
CHR: prim-call-bitnot @ // { PrimCall ?w { ?x } { ?y } } -- [ ?w { bignum-bitnot fixnum-bitnot } in? ] | { BitNot ?y ?x } ;
CHR: prim-call-fixnum> @ // { PrimCall ?w { ?x } { ?y } } -- [ ?w { fixnum>float fixnum>bignum } in? ] | { Num= ?x ?y } ;
CHR: prim-call-shift @ // { PrimCall fixnum-shift { ?x ?n } { ?y } } -- | { Shift ?y ?x ?n } ;

! ** Composition mode expansions
PREFIX-RULES: { P{ CompMode } }

! *** Cloning

! NOTE: The class pred there has implied directional semantics here, not sure if that is important
CHR: prim-call-clone @ // { PrimCall (clone) L{ ?x . ?a } L{ ?y . ?a } } -- |
{ Eq ?x ?y } { LocalAllocation ?y } { ClassPred ?y ?x class= } ;

! *** Locals
! [| a b | a ] -> [ 2 load-locals -1 get-local 2 drop-locals ]


:: ensure-retain-stack ( n -- list )
    ! "rest" utermvar :> tail
    n [ "pad" utermvar ] replicate >list ;

! L{ ?x . ?a } --> L{ r( ?x ) . ?a } ???

CHR: do-load-local @ // { PrimCall load-local L{ ?x . ?a } ?b } -- |
{ PolyEffect R ?a ?rho L{ ?x . ?rho } ?b } ;

CHR: do-load-locals @ // { PrimCall load-locals L{ ?n . ?a } ?b } { Eq ?n A{ ?v } } --
[ ?v ensure-retain-stack :>> ?l ] |
[| | ?l ?rho list* :> sout
 ?l ?c list* ?a ==!
 P{ PolyEffect R ?c ?rho sout ?b } 2array
] ;

CHR: do-drop-locals @ // { PrimCall drop-locals L{ ?n . ?a } ?b } { Eq ?n A{ ?v } } --
[ ?v ensure-retain-stack :>> ?l ] |
[| | ?l ?rho list* :> sin
 P{ PolyEffect R ?a sin ?rho ?b } ] ;

CHR: do-get-local @ // { PrimCall get-local L{ ?n . ?a } L{ ?x . ?b } } { Eq ?n A{ ?v } } --
[ ?v neg ensure-retain-stack :>> ?l ] |
[| | ?l ?x ?rho cons lappend :> sinout
 P{ PolyEffect R ?a sinout sinout ?b } ] ;



;
