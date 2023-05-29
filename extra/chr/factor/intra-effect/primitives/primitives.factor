USING: chr.factor chr.parser classes.algebra kernel lists locals.backend math
math.private sequences sets terms types.util ;

IN: chr.factor.intra-effect.primitives

! * Primitive Expansions


CHRAT: chr-factor-prim { }

! *** Math Prim Conversions
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
    "rest" utermvar :> tail
    n [ "pad" utermvar ] replicate >list tail list* ;

CHR: do-load-local @ // { PrimCall load-local L{ ?x . ?a } ?b } -- |
{ RetainEffect L{ ?x . ?a } ?b ?rho L{ ?x . ?rho } } ;

CHR: do-load-locals @ // { PrimCall load-locals L{ ?n . ?a } ?b } { Eq ?n A{ ?v } } --
[ ?v ensure-retain-stack :>> ?o ]
[ ?o lastcdr :>> ?i ] | { RetainEffect L{ ?n . ?a } ?b ?i ?o } ;

CHR: do-drop-locals @ // { PrimCall drop-locals L{ ?n . ?a } ?b } { Eq ?n A{ ?v } } --
[ ?v ensure-retain-stack :>> ?i ]
[ ?i lastcdr :>> ?o ] | { RetainEffect L{ ?n . ?a } ?b ?i ?o } ;

CHR: do-get-local @ // { PrimCall get-local L{ ?n . ?a } L{ ?x . ?a } } { Eq ?n A{ ?v } } --
[ ?x ?v neg ensure-retain-stack cons :>> ?l ]
| { RetainStack ?a ?l } ;



;
