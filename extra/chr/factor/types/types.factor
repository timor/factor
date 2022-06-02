USING: chr chr.factor chr.factor.terms chr.parser classes classes.algebra kernel
terms ;

IN: chr.factor.types
FROM: chr => val-pred ;

! Partial order
TUPLE: sub < type-pred t1 t2 ;
TUPLE: Instance < val-pred type ;


CHRAT: chr-types {  }

CHR: null-instance-is-failure @ // { Instance __ null } -- | false ;


CHR: lit-instance @ Is{ ?b ?v } // -- [ ?v ground-value? ] [ ?v class-of :>> ?tau ] |
{ Instance ?b ?tau } ;

    ! A Set union relation
    ! TUPLE: Union < type-pred x y res ;
CHR: check-literal-instance @ // { Instance A{ ?v } A{ ?tau } } -- | [ ?v ?tau instance? [ f ] [ false ] if ] ;
! ! NOTE: This looks flimsy at first, but for value-set semantics, values are special instances of ">singleton" types
! ! TODO: make sure words are quoted correctly here!
! CHR: check-literal-subtype @ { sub A{ ?x } A{ ?tau } } // -- |
! [ ?x classoid? [ ?x ?tau class<= [ "notsub" throw ] unless ]
!   [ ?x ?tau instance? [ "notsubinst" throw ] unless ] if
!   f
! ] ;

! ! CHR: literal-def-is-instance @ Is{ ?x A{ ?v } } // -- [ ?v class-of :>> ?tau ] | { Instance ?x ?tau }

! CHR: unique-instance @ { Instance ?x ?tau } // { Instance ?x ?tau } -- | ;

! CHR: unique-sub @ { sub ?x ?tau } // { sub ?x ?tau } -- | ;

! CHR: union-instance @ // { C True{ ?c } P{ Instance ?x A{ ?tau } } } { C False{ ?c } P{ Instance ?x A{ ?sig } } } -- [ ?tau ?sig class-or :>> ?y ] |
! { Instance ?x ?y } ;

;
