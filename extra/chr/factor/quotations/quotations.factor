USING: accessors arrays chr chr.factor chr.factor.defs chr.factor.effects
chr.factor.terms chr.parser chr.state classes combinators
combinators.short-circuit kernel lists math.parser quotations sequences strings
terms types.util words words.symbol ;

IN: chr.factor.quotations
FROM: syntax => _ ;
FROM: chr.factor.terms => val-pred ;
FROM: chr.factor.types => Instance ;
FROM: chr.factor.effects => Effect ;

! * Quotation Inference

GENERIC: elt>var ( i elt -- obj )
M: f elt>var drop number>string "v" prepend utermvar ;
M: string elt>var nip utermvar ;
M: pair elt>var
    first2 drop elt>var ;

: elt-vars ( seq -- seq )
    [ swap elt>var ] map-index ;
! [ swap dup pair? [ first ] when
!   [ nip ] [ number>string "v" prepend ] if*
!   uvar
!   <term-var>
! ] map-index <reversed> ;

: effect>stack-elts ( effect -- lin lout )
    [ in>> elt-vars <reversed> >list ]
    [ out>> elt-vars <reversed> >list ] bi ;

:: add-row-vars ( lin lout effect -- lin lout )
    effect [ in-var>> ] [ out-var>> ] bi
    [ dup [ utermvar ] when ] bi@
    :> ( i o )
    { { [ i o [ not ] both? ]
        [ "rho" utermvar :> rho
          lin rho list*
          lout rho list* ] }
      { [ i o [  ] both? ]
        [ lin i list*
          lout o list* ] }
      [ lin __ list* lout __ list* ]
    } cond ;

: effect>stacks ( effect -- lin lout )
    [ effect>stack-elts ]
    [ add-row-vars ] bi ;

TUPLE: Transeq < chr-pred from to quot ;
TUPLE: Trans < chr-pred from to command ;
<PRIVATE
TUPLE: BuildQuot < chr-pred from to quot ;
PRIVATE>
TUPLE: BuildNamedQuot < BuildQuot var ;
TUPLE: Mark < chr-pred ctx val ;
TUPLE: Marked < chr-pred ctx vals ;

PREDICATE: quot-sym < word "quot-id" word-prop? ;
: <quot-sym> ( name -- word ) usym dup t "quot-id" set-word-prop ;

PREDICATE: callable-word < word { [ symbol? not ] [ quot-sym? not ] } 1&& ;
! PREDICATE: callable-word < word symbol? not ;


CHRAT: chr-quot { }

CHR: stack-match @ { Stack ?s ?a } // { Stack ?s ?b } -- | [ ?a ?b ==! ] ;
CHR: empty-quot @ // { Transeq ?s ?t [ ] } -- | [ ?s ?t ==! ] ;
CHR: destructure-quot @ // { Transeq ?s ?t ?p } -- [ ?p first dup callable-word? [ <wrapper> ] unless :>> ?w ?p rest :>> ?q ?s seq-state :>> ?s0 3drop t ] |
{ Transeq ?s0 ?t ?q }
{ Trans ?s ?s0 ?w } ;

! ! Early replacement
CHR: inline-if @ // { Trans ?s ?t if } -- | { Transeq ?s ?t [ ? call ] } ;


! Effect-based destructuring
CHR: effect-predicate @ { Trans ?s ?t A{ ?w } } // -- [ ?w callable-word? ]
[ ?w defined-effect :>> ?e ]
[ ?e effect>stacks [ :>> ?a ] [ :>> ?b ] bi* 2drop t ]
|
{ Stack ?s ?a }
{ Stack ?t ?b }
{ Eval ?w ?a ?b }
    ;

! CHR: do-infer-inline @ { Literal ?n A{ ?p } } { Trans ?s ?t call } // { Eval call ?n ?a ?b } -- [ ?p :>> ?q ] |
! CHR: do-infer-inline @ { Literal ?n A{ ?p } } // { Eval call L{ ?n . ?a } ?b } -- [ ?p :>> ?q ] |
! { Stack ?s ?a }
! { Stack ?t ?b }
! { BuildQuot ?s ?t ?q } ;
! ! { InferEffect ?n f ?a ?b } ;
! ! ! { InferEffect ?n f ?a ?b f }
! ! { Mark ?n ?s }
! ! { Mark ?n ?t }
! ! { Marked ?n f } ;
! ! ! { InferDone ?n } ;
TERM-VARS: Quot ;

CHR: push-literal @ { Trans ?s ?t A{ ?w } } // -- ! [ break ?v wrapper? ] [ ?v wrapped>> :>> ?w drop t ]
[ ?w callable-word? not ] [ ?w :>> ?v class-of :>> ?tau ] |
{ Stack ?s ?xs }
{ Literal ?x ?v }
{ Instance ?x ?tau }
{ Stack ?t L{ ?x . ?xs } }
! { Instance ?x ?tau }
    ;

CHR: push-quot @ { Trans ?s ?t A{ ?q } } // -- [ ?q callable? ] |
{ Stack ?s ?xs }
{ Stack ?t L{ Quot . ?xs } }
{ Stack ?rho ?a }
{ Stack ?sig ?b }
{ BuildNamedQuot ?rho ?sig ?q Quot }
{ Effect Quot f ?a ?b f }
    ;


CHR: build-empty-quot @ // { BuildQuot ?s ?t [ ] } -- |
{ Stack ?s ?rho } { Stack ?t ?rho } ;

CHR: build-named-quot @ // { BuildNamedQuot ?s ?t ?q ?n } -- |
{ BuildQuot ?s ?t ?q } ;
! { Mark ?n ?s }
! { Mark ?n ?t }
! { Marked ?n f } ;

CHR: build-quot-body @ // { BuildQuot ?s ?t ?q } -- |
{ Transeq ?s ?t ?q }
{ Mark ?m ?s }
{ Mark ?m ?t }
{ Marked ?m f } ;


! ** Cleanup
CHR: mark-once @ { Mark ?k ?x } // { Mark ?k ?x } -- | ;
CHR: mark-sweep-trans @ { Mark ?k ?s } // { Trans ?s ?t __ } -- | { Mark ?k ?t } ;
CHR: mark-stack @ { Mark ?k ?s } // { Stack ?s ?x } -- | [ ?x vars [ ?k swap Mark boa ] map ] ;

CHR: collect-marks @ // { Marked ?k ?a } { Mark ?k ?x } -- [ ?a ?x suffix :>> ?b drop t ] | { Marked ?k ?b } ;
! CHR: sweep-leftover-effects @ { Marked ?w ?a } // AS: ?p P{ Effect ?q __ __ __ __ } --
! [ ?q ?w == not ] [ ?q ?a in? ] | ;
! CHR: sweep-leftover @ { Marked __ ?a } // AS: ?p <={ type-pred } -- [ ?p free-vars ?a subset? ] | ;
CHR: end-mark @ // { Marked __ __ } -- | ;

    ;
