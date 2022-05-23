USING: accessors arrays assocs chr chr.comparisons chr.factor
chr.factor.conditions chr.factor.defs chr.factor.effects chr.factor.quotations
chr.factor.terms chr.factor.types chr.parser chr.state classes classes.algebra
classes.tuple combinators combinators.short-circuit effects generic.math
grouping kernel kernel.private lists match math math.parser namespaces
quotations sequences sequences.deep sets strings terms types.util vectors words
words.symbol ;

IN: chr.factor.direct
FROM: syntax => _ ;
FROM: chr.factor.terms => val-pred ;
FROM: chr.factor.effects => Effect ;
FROM: chr.factor.types => Instance ;


TUPLE: BuildEffectType < chr-pred name quot ;
! TUPLE: DefCallRule < chr-pred name start end ;
TUPLE: DefCallRule < chr-pred name start end body ;
TUPLE: AddRule < chr-pred rule ;
TUPLE: TransRule < chr-pred head body ;

! Callable Stuff
TUPLE: Call < chr-pred quot in out ;
! Slightly delayed...
TUPLE: EffectCall < Effect from to ;
TUPLE: RecursiveCall < type-pred quot in out ;
TUPLE: InferDone < chr-pred word ;
TUPLE: RebuildEffect < InferEffect ;
TUPLE: ApplyEffects < chr-pred word tags in out ;
TUPLE: PerformCall < chr-pred call-pred effect-pred ;
TUPLE: EffectGen < chr-pred word in out body ;

! These can never be polymorphically different!
! TUPLE: Literal < chr-pred name quot ;

! Val stuff
TUPLE: Sum < val-pred x y ;
! TUPLE: Drop < chr-pred val ;
TUPLE: Dup < chr-pred val copy ;
TUPLE: Drop < chr-pred val ;
! TUPLE: Use < val-pred ;

TUPLE: Lt < val-pred x ;
TUPLE: Le < val-pred x ;
TUPLE: Gt < val-pred x ;
TUPLE: Ge < val-pred x ;
TUPLE: Eq < val-pred x ;
TUPLE: Is < val-pred x ;

! Types with constructors.
! Those can appear in effects as syntactic matches
TUPLE: Tuple < type-pred ;
    ! Expressions.
TUPLE: Expr < val-pred term ;

! Cleanup
TUPLE: Used < chr-pred val ;

! Conditional Stuff

! Type Stuff
! TUPLE: Provide < chr-pred val type ;
! TUPLE: Require < chr-pred val type ;

! Var stuff
! NOTE: there's still an open question here regarding free vars for instatiation
! and scoping...
! : effect-bound-vars ( x -- x )
!     ! [ parms>> ] [ in>> vars union ] [ out>> vars union ] tri ;
!     ! [ parms>> ] [ in>> vars union ] bi ;
!     [ in>> vars ] [ out>> vars union ] bi ;

: effect-bound-vars ( x -- x )
    [ in>> vars ] [ out>> vars ]
    [ constraints>> bound-vars ] tri union union ;

: effect-free-vars ( x -- x )
    [
        { [ parms>> vars ] [ in>> vars union ] [ out>> vars union ]
          [ constraints>> free-vars union ] } cleave
    ] [ bound-vars diff ] bi ;


    ! [ vars ] [ bound-vars diff ] bi ;
    ! [ constraints>> free-vars ] [ bound-vars diff ] [ word>> ] tri suffix ;

M: Effect bound-vars effect-bound-vars ;
M: Effect free-vars effect-free-vars ;
M: InferEffect bound-vars effect-bound-vars ;
M: InferEffect free-vars effect-free-vars ;

TERM-VARS: Q ;
TERM-VARS: top end ;

CHRAT: quots { }
IMPORT: chrat-comp
IMPORT: chr-cond
IMPORT: chr-types
IMPORT: chr-quot
IMPORT: chr-effects


! ** Value Predicates
! Redundancies
CHR: unique-val-preds @ AS: ?p <={ val-pred ?x . ?xs } // AS: ?q <={ val-pred ?x . ?xs } --
[ ?p ?q [ class-of ] same? ] | ;

! Early drops
CHR: drop-lit-type-preds @ { Drop ?x } { Literal ?x __ } // AS: ?p <={ type-pred } -- [ ?x ?p vars in? ] | ;
CHR: drop-lit @ { Drop ?q } // { Literal ?q __ } -- | ;

! CHR: unique-use @ { Use ?x } // { Use ?x } -- | ;

! TODO: same things backward if e.g. interval propagation turned out to know an exact value
CHR: lit-trans-is-lit-forward @ { Literal ?x __ } // { Is ?x ?y } -- | [ ?y ?x ==! ] ;

CHR: trans-val-preds-forward @ <={ Is ?x ?y } AS: ?p <={ val-pred ?x . ?xs } // -- |
[ ?p clone ?y >>val ] ;

CHR: trans-val-preds-backward @ <={ Is ?y ?x } AS: ?p <={ val-pred ?x . ?xs } // -- |
[ ?p clone ?y >>val ] ;

CHR: dup-val-preds-forward @ <={ Dup ?x ?y } AS: ?p <={ val-pred ?x . ?xs } // -- |
[ ?p clone ?y >>val ] ;

CHR: dup-val-preds-backward @ <={ Dup ?y ?x } AS: ?p <={ val-pred ?x . ?xs } // -- |
[ ?p clone ?y >>val ] ;

! Cleanup

! CHR: drop-implies-use @ // { Drop ?x } -- | { Use ?x } ;
! CHR: used-use-literal @ // { Use A{ ?x } } -- | ;
! CHR: used-used-literal @ // { Used A{ ?x } } -- | ;
! CHR: check-literal-require @ // { Require A{ ?x } A{ ?tau } } -- |
! [ ?x ?tau instance? [ "nope" throw ] unless f ] ;
! CHR: check-literal-provide @ // { Provide A{ ?x } A{ ?tau } } -- |
! [ ?x ?tau instance? [ "nopenope" throw ] unless f ] ;

! TODO: possibly only do for lifts, but then again this would be a val pred, no?
CHR: dropped-effect @ { Drop ?q } // { Effect ?q __ __ __ __ } -- | ;

! ** Value/Conditional reasoning
! CHR: destructure-cases @ // P{ Cases ?l } -- | [ ?l [ unclip swap Case boa ] map ] ;
! CHR: exclude-false-case @ False{ ?c } // Case{ True{ ?c } __ } -- | ;
! CHR: exclude-true-case @ True{ ?c } // Case{ False{ ?c } __ } -- | ;
! CHR: preempt-false-case @ False{ ?c } // Case{ False{ ?c } ?r } -- | [ ?r ] ;
! CHR: preempt-true-case @ True{ ?c } // Case{ True{ ?c } ?r } -- | [ ?r ] ;

! CHR: split-true-case @ // { Case ?p ?l } -- |
! Cond{ { ?p ?l } { f f } } ;

CHR: known-false-case @ False{ ?c } // { IfTe ?c ?p ?q } -- | [ ?q ] ;
CHR: known-true-case @ True{ ?c } // { IfTe ?c ?p ?q } -- | [ ?p ] ;
CHR: unknown-case @ // { IfTe ?c ?p ?q } -- |
Cond{ { False{ ?c } { False{ ?c } ?q } }
      { True{ ?c } { True{ ?c } ?p } }
    } ;

! CHR: lift-tautologies @ // { C ?c ?x } { C Not{ ?c } ?x } -- |
! [ ?x ] ;
! CHR: double-negation @ // { C Not{ Not{ ?c } } ?k } -- | { C ?c ?k } ;

! CHR: distribute-last-cond @ { C { ?c } ?p } // -- | { C ?c ?p } ;


CHR: redundant-definition @ // { Literal A{ ?v } A{ ?v } } -- | ;

: xor-tags ( tags1 tags2 -- tags1 )
    [ [ neg ] dip in? ] curry reject ;

: lift-tags ( tags1 tags2 -- tags/f )
    [ xor-tags ]
    [ swap xor-tags ] 2bi
    over set= [ drop f ] unless ;

! CHR: import-sub-predicates @ { InferEffect ?w ?c ?a ?b __ } { Effect ?w ?d ?x ?y ?k } // -- [ ?c ?d intersects? ] [ { ?x ?y } { ?a ?b } [ solve-eq ] no-var-restrictions :>> ?m ] |
! [ ?k ?m lift [ ?c swap C boa ] map ]
!     ;


! ** Apply Effects at call sites

! Here be special per-word stuff

CHR: apply-dip-effect @ // { Eval dip L{ ?w ?x . ?a } L{ ?y . ?b } } -- |
[ ?x ?y ==! ]
{ Call ?w ?a ?b } ;

! TODO: check if it is necessary to do this on trans?
! CHR: call-declares-effect @ { Trans ?r ?u call } { Stack ?r L{ ?w . ?a } } { Stack ?u ?b } // -- |
! { Effect ?w f ?a ?b f } ;
! If a new Call is there, it will declare an effect.  This in turn will trigger re-inference.
! Does not apply to recursive calls.

! CHR: recursive-call @ { Call ?x ?a ?b } // -- [ ?x ?a vars in? ] | { RecursiveCall ?x ?a ?b } ;
CHR: duplicate-call @ { Call ?q ?a ?b } // { Call ?q ?a ?b } -- | ;

! CHR: call-declares-effect @ { Call ?q ?a ?b } // -- | { Effect ?q f ?a ?b f } ;

! CHR: perform-call-effect @ { Effect ?q ?c ?x ?y ?l } // { Call ?q ?a ?b } -- |
! Assuming multiple possible effects here
! Re-inference semantics
CHR: apply-call-effect @ { Call ?q ?a ?b } // { Effect ?q ?c ?x ?y ?l } -- |
! { EffectCall ?q ?c ?x ?l ?a ?b } ;
! [ { ?x ?y } { ?a ?b } ==!  ]
[ { ?a ?b } { ?x ?y } ==!  ]
! [ { ?x ?b } { ?a ?y } ==!  ]
[ ?l ] ;
! [ ?l { ?x ?y } { ?a ?b } unify lift ] ;
! { InferEffect ?q ?c ?a ?b f } ;

CHR: lit-call-effect @ // { Literal ?q __  } { Call ?q ?a ?b } -- | { Drop ?q } ;

CHR: re-infer-call-effect @ // { Call ?q ?a ?b } -- |
{ Effect ?q f ?a ?b f }
! Cond{ { f f }
!       { f { P{ InferEffect ?q f ?a ?b f } } } }
 ;


CHR: do-call @ // { Eval call L{ ?q . ?a } ?b } -- | { Call ?q ?a ?b } ;

CHR: math-uses-numbers @ { Eval ?w L{ ?x ?y . __ } __ } // -- [ ?w math-generic? ] |
{ Instance ?x number }
{ Instance ?y number } ;

CHR: plus-is-sum @ { Eval + L{ ?x ?y . __ } L{ ?z . __ } } // -- |
{ Instance ?z number }
{ Sum ?x ?y ?z } ;

! : > ( y x -- c ) c=t <-> y > x, c=f <-> y <= x
CHR: ge-defines-ge @ { Eval > L{ ?x ?y . __  } L{ ?c . __ } } // -- |
{ IfTe ?c
  { P{ Le ?y ?x } }
  { P{ Lt ?x ?y } }
 } ;

! : < ( y x -- c ) c=t <-> y < x, c=f <-> y >= x
CHR: le-defines-le @ { Eval > L{ ?x ?y . __  } L{ ?c . __ } } // -- |
{ IfTe ?c
  { P{ Le ?x ?y } }
  { P{ Lt ?y ?x } }
} ;


! *** Currying
! Two approaches:
! 1. Declare the incoming effect to actually have a parameter.
! Problem: curry would then modify existing effects, which is a problem when
! they are dup'ed, because that is actually not cloning.  We could treat it like
! cloning, but that might mess up existing free-var semantics.
! 2. Make the curried effect a function of the incoming one
! It still declares an effect of the incoming quot, though.

CHR: do-unit @ // { Eval 1quotation L{ ?x . __ } L{ ?q . __ } } -- |
{ Effect ?q f ?a L{ ?x . ?a } f } ;
! { InferEffect ?q { ?x } ?a L{ ?x . ?a } f } ;
! { InferEffect ?q f ?a L{ ?x . ?a } f } ;

CHR: do-compose @ // { Eval compose L{ ?q ?p . __ } L{ ?k . __ } } -- |
! { Effect ?q f ?a ?b f }
! { InferEffect ?k f ?a ?c f }
{ Call ?p ?a ?b }
{ Call ?q ?b ?c }
! ! { Effect ?p f ?a ?b f }
! ! { Effect ?q f ?b ?c f }
! !  { Effect ?k f ?a ?c f }
{ Effect ?k f ?a ?c f } ;
! { InferDone ?k }
!     ;

! Basic data flow

: effect-dups ( effect -- assoc )
    [ in>> ] [ out>> ] bi
    [| elt index out | index elt out indices ?rest 2array ] curry map-index ;

: effect-ops ( effect -- assoc )
    [ in>> ] [ out>> ] bi
    [| elt index out | index elt out indices 2array ] curry map-index ;

:: effect>drops ( in effect -- res )
    effect [ in>> elt-vars ] [ dupd shuffle ] bi :> ( in-vars out-vars )
    V{ } clone
    in-vars [ dup out-vars in? [ drop __ ] [ dup Drop boa pick push ] if ] map
    over empty? [ 2drop f ]
    [ >list __ list* in [ ==! ] 2curry prefix ] if
    ;

! Non-drop version
! : effect>ops ( in out effect -- seq )
!     effect-ops
!     [| ins outs op | op first2 :> ( i os )
!      os [ f ] [ [| o | i ins nth o outs nth is boa ] map ] if-empty
!     ] 2with gather ;

! Drop/dup version
: effect>ops ( in out effect -- seq )
    effect-ops
    [| ins outs op | op first2 :> ( i os )
     i ins nth :> in-var
     os
     [ in-var Drop boa 1array ]
     [ [ first outs nth in-var Is boa 1array ]
       [ 2 <clumps> [ first2 swap [ outs nth ] bi@ Dup boa suffix ] each ] bi
     ] if-empty
    ] 2with gather ;

! CHR: shuffle-drops @ { Eval ?w ?a ?b } // -- [ ?w "shuffle" word-prop :>> ?e ] |
! [ ?a ?e effect>drops ] ;

! CHR: do-shuffle-direct @ // { Eval ?w ?a ?b } -- [ ?w "shuffle" word-prop :>> ?e ] |
! [
!  ?e in>> elt-vars dup ?e shuffle [ <reversed> >list __ list* ] bi@ 2array { ?a ?b } ==!
! ] ;

CHR: do-shuffle-alias @ // { Eval ?w ?a ?b } -- [ ?w "shuffle" word-prop :>> ?e ] |
[
    ?a list>array* ?b list>array* [ <reversed> ] bi@ ?e effect>ops
] ;

! CHR: do-mux-infer-dispatch @ // { Eval ? L{ ?q ?p ?c . __ } L{ ?v . __ } } -- [ J counter :>> ?n neg :>> ?m ] |
! Cond{
!     ! { True{ ?c } { [ ?c not{ POSTPONE: f } ==! ] [ ?v ?p ==! ] } }
!     ! { False{ ?c } { [ ?c \ f ==! ] [ ?v ?q ==! ] } }
!     { False{ ?c } { False{ ?c } [ ?q ?v ==! ] P{ Drop ?p } P{ Instance ?c POSTPONE: f } } }
!     { True{ ?c } { True{ ?c } [ ?p ?v ==! ] P{ Drop ?q } P{ Instance ?c not{ POSTPONE: f } } } }
! }
! ! { Use ?c }
!     ;

! CHR: do-mux @ // { Eval ? L{ ?q ?p ?c . __ } L{ ?v . __ } } -- [ J counter :>> ?n neg :>> ?m ] |
! Cases{
!     { False{ ?c } { False{ ?c } [ ?q ?x ==! ] P{ Drop ?p } P{ Instance ?c POSTPONE: f } P{ Is ?v ?x } } }
!     { True{ ?c } { True{ ?c } [ ?p ?y ==! ] P{ Drop ?q } P{ Instance ?c not{ POSTPONE: f } } P{ Is ?v ?y } } }
! }
! ! { Use ?c }
!     ;
! CHR: do-mux @ // { Eval ? L{ ?q ?p ?c . __ } L{ ?v . __ } } -- |
! { IfTe ?c
!   ! { [ ?p ?y ==! ] P{ Drop ?q } P{ Instance ?c not{ POSTPONE: f } } P{ Is ?v ?y } }
!   ! { [ ?q ?x ==! ] P{ Drop ?p } P{ Instance ?c POSTPONE: f } P{ Is ?v ?x } }
!   { [ ?p ?v ==! ] P{ Drop ?q } P{ Instance ?c not{ POSTPONE: f } } }
!   { [ ?q ?v ==! ] P{ Drop ?p } P{ Instance ?c POSTPONE: f } }
! } ;

CHR: do-mux-ref @ // { Eval ? L{ ?q ?p ?c . __ } L{ ?v . __ } } -- |
{ IfTe ?c
  ! { [ ?p ?y ==! ] P{ Drop ?q } P{ Instance ?c not{ POSTPONE: f } } P{ Is ?v ?y } }
  ! { [ ?q ?x ==! ] P{ Drop ?p } P{ Instance ?c POSTPONE: f } P{ Is ?v ?x } }
  { P{ Is ?v ?p } P{ Drop ?q } P{ Instance ?c not{ POSTPONE: f } } }
  { P{ Is ?v ?q } P{ Drop ?p } P{ Instance ?c POSTPONE: f } }
} ;

! Predicate words
CHR: add-predicate-rules @ { Eval ?w L{ ?v . __ } L{ ?c . __ } } // --
[ ?w "predicating" word-prop :>> ?tau ] |
[| |
 ?tau :> then-class
 ?tau class-not :> else-class
    { IfTe ?c
      P{ Instance ?v then-class }
      P{ Instance ?v else-class }
    }
]
! { Use ?v }
    ;

! Declarations
! NOTE: Only doing provide here, which is in effect a down-cast
CHR: do-declare @ { Literal ?x A{ ?tau } } // { Eval declare L{ ?x . ?a } ?b } -- |
[| |
 ?tau length [ "v" utermvar ] replicate :> vars
 vars >list ?rho list* :> var-stack
 [ ?b var-stack ==! ]
 [ ?a var-stack ==! ] 2array
 vars ?tau [ sub boa ] 2map append
]
! { Use ?x }
    ;


! Convert anything that is left into an expression if possible
CHR: make-expression @ // { Eval ?w ?i ?o } -- [ ?w inline? not ] [ ?w stack-effect out>> length 1 = ] |
[| | ?w stack-effect in>> length :> arity
 ?i list>array* arity head :> args
 ?o car :> out-var
 args ?w prefix :> term
 P{ Expr out-var term }
] ;

! ** Subordinate inference
! Entry point for anonymous quotations
CHR: build-named-call-effect @ // { BuildEffectType ?n A{ ?p } } -- [ ?p :>> ?q ] |
{ Stack top ?a }
{ Stack end ?b }
{ BuildNamedQuot top end ?q ?n }
{ Effect ?n f ?a ?b f }
! { InferDone Q }
    ;


! For in-domain simulation
! CHR: call-uncall @ // { ReInferEffect ?q ?c ?a ?b ?k }

! Collect predicates
DEFER: make-simp-rule

: group-conditionals ( body -- body )
    [ C? ] partition swap
    [ cond>> ] collect-by
    [ [ then>> ] map >array C boa suffix ] assoc-each
    ;

! Cleanup used vals

! CHR: used-definition-is-lit @ { Literal ?x A{ ?v } } // { Use ?x } -- |
! [ ?v callable? not [ ?x ?v ==! ] [ f ] if ]
! { Used ?x } ;

CHR: finish-infer-effect-simple @ // { InferEffect ?n ?c ?a ?b ?k } -- |
{ Effect ?n ?c ?a ?b ?k } ;
;

! * External

: build-quot-rule ( thunk name -- chrs )
    swap BuildEffectType boa 1array quots swap run-chr-query store>> ;

:: make-simp-rule ( heads body word -- rule )
    word name>> :> wname
    wname "-call" append :> rname
    heads 0 f body f named-chr new-chr rname >>rule-name ;

GENERIC: build-type ( word -- chrs )
M: callable build-type
    "anon" utermvar build-quot-rule ;
M: word build-type
    [ def>> ] keep swap BuildEffectType boa 1array quots swap run-chr-query store>> ;
