USING: accessors arrays assocs chr chr.comparisons chr.factor
chr.factor.conditions chr.factor.defs chr.factor.effects chr.factor.quotations
chr.factor.terms chr.factor.types chr.parser chr.state classes classes.algebra
classes.tuple combinators combinators.short-circuit effects generic.math kernel
kernel.private lists match math math.parser namespaces quotations sequences
sequences.deep sets strings terms types.util vectors words words.symbol ;

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
TUPLE: Dup < val-pred copy ;
TUPLE: Drop < chr-pred val ;
TUPLE: Use < val-pred ;

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

! Early drops
CHR: drop-def @ { Drop ?q } // { Literal ?q __ } -- | ;

CHR: unique-use @ { Use ?x } // { Use ?x } -- | ;

! Cleanup
CHR: drop-type-preds @ { Drop ?x } // AS: ?p <={ type-pred } -- [ ?x ?p vars in? ] | ;

! CHR: drop-implies-use @ // { Drop ?x } -- | { Use ?x } ;
CHR: used-use-literal @ // { Use A{ ?x } } -- | ;
CHR: used-used-literal @ // { Used A{ ?x } } -- | ;
! CHR: check-literal-require @ // { Require A{ ?x } A{ ?tau } } -- |
! [ ?x ?tau instance? [ "nope" throw ] unless f ] ;
! CHR: check-literal-provide @ // { Provide A{ ?x } A{ ?tau } } -- |
! [ ?x ?tau instance? [ "nopenope" throw ] unless f ] ;
CHR: dropped-effect @ { Drop ?q } // { Effect ?q __ __ __ __ } -- | ;

! ** Value/Conditional reasoning
! CHR: lift-tautologies @ // { C ?c ?x } { C Not{ ?c } ?x } -- |
! [ ?x ] ;
! CHR: double-negation @ // { C Not{ Not{ ?c } } ?k } -- | { C ?c ?k } ;

! CHR: distribute-last-cond @ { C { ?c } ?p } // -- | { C ?c ?p } ;


! CHR: instance-union @ J{ ?m P{ Instance ?v A{ ?tau } } } J{ ?n P{ Instance ?v A{ ?sig } } } // -- [ ?m neg ?n = ] [ ?tau ?sig class-or :>> ?c ] |
! { Instance ?v ?c } ;

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
! [ ?l ]
[ ?l { ?x ?y } { ?a ?b } unify lift ] ;
! { InferEffect ?q ?c ?a ?b f } ;

CHR: re-infer-call-effect @ // { Call ?q ?a ?b } -- |
{ InferEffect ?q f ?a ?b f }
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
{ InferEffect ?k f ?a ?c f } ;
! { InferDone ?k }
!     ;

! Basic data flow

: effect-dups ( effect -- assoc )
    [ in>> ] [ out>> ] bi
    [| elt index out | index elt out indices ?rest 2array ] curry map-index ;

:: effect>drops ( in effect -- res )
    effect [ in>> elt-vars ] [ dupd shuffle ] bi :> ( in-vars out-vars )
    V{ } clone
    in-vars [ dup out-vars in? [ drop __ ] [ dup Drop boa pick push ] if ] map
    over empty? [ 2drop f ]
    [ >list __ list* in [ ==! ] 2curry prefix ] if
    ;

CHR: shuffle-drops @ { Eval ?w ?a ?b } // -- [ ?w "shuffle" word-prop :>> ?e ] |
[ ?a ?e effect>drops ] ;

! TBR?
CHR: do-shuffle-direct @ // { Eval ?w ?a ?b } -- [ ?w "shuffle" word-prop :>> ?e ] |
[
 ?e in>> elt-vars dup ?e shuffle [ <reversed> >list __ list* ] bi@ 2array { ?a ?b } ==!
] ;

CHR: do-mux-infer-dispatch @ // { Eval ? L{ ?q ?p ?c . __ } L{ ?v . __ } } -- [ J counter :>> ?n neg :>> ?m ] |
Cond{
    ! { True{ ?c } { [ ?c not{ POSTPONE: f } ==! ] [ ?v ?p ==! ] } }
    ! { False{ ?c } { [ ?c \ f ==! ] [ ?v ?q ==! ] } }
    { False{ ?c } { False{ ?c } [ ?q ?v ==! ] P{ Drop ?p } P{ Instance ?c POSTPONE: f } } }
    { True{ ?c } { True{ ?c } [ ?p ?v ==! ] P{ Drop ?q } P{ Instance ?c not{ POSTPONE: f } } } }
}
! { Use ?c }
    ;

! Predicate words
CHR: add-predicate-rules @ { Eval ?w L{ ?v . __ } L{ ?c . __ } } // --
[ ?w "predicating" word-prop :>> ?tau ] |
[| |
 ?tau :> then-class
 ?tau class-not :> else-class
    Cond{ { False{ ?c } { False{ ?c } P{ Instance ?v else-class } } }
          { True{ ?c } { True{ ?c } P{ Instance ?v then-class } } }
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
] { Use ?x } ;


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
{ InferEffect ?n f ?a ?b f }
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
