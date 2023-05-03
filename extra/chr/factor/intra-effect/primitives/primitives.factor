USING: chr.factor chr.parser math.private sets ;

IN: chr.factor.intra-effect.primitives

! * Primitive Expansions


CHRAT: chr-factor-prim { }

! *** Prim Conversions
CHR: prim-call-bitnot @ // { PrimCall ?w { ?x } { ?y } } -- [ ?w { bignum-bitnot fixnum-bitnot } in? ] | { BitNot ?y ?x } ;
CHR: prim-call-fixnum> @ // { PrimCall ?w { ?x } { ?y } } -- [ ?w { fixnum>float fixnum>bignum } in? ] | { Num= ?x ?y } ;
CHR: prim-call-shift @ // { PrimCall fixnum-shift { ?x ?n } { ?y } } -- | { Shift ?y ?x ?n } ;


;
