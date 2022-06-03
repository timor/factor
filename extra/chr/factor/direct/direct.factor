USING: accessors arrays assocs chr chr.comparisons chr.factor
chr.factor.conditions chr.factor.defs chr.factor.effects chr.factor.quotations
chr.factor.terms chr.factor.types chr.parser chr.state classes classes.algebra
classes.tuple combinators combinators.short-circuit effects generic.math
grouping kernel kernel.private lists match math math.parser namespaces
quotations sequences sequences.deep sets strings terms types.util vectors words
words.symbol ;

IN: chr.factor.direct
FROM: syntax => _ ;
FROM: chr => val-pred ;
FROM: chr.factor.terms => Call ;
FROM: chr.factor.effects => Effect ;
FROM: chr.factor.types => Instance ;


TUPLE: BuildEffectType < chr-pred name quot ;
! TUPLE: DefCallRule < chr-pred name start end ;
TUPLE: DefCallRule < chr-pred name start end body ;
TUPLE: AddRule < chr-pred rule ;
TUPLE: TransRule < chr-pred head body ;

! Callable Stuff
! Slightly delayed...
TUPLE: EffectCall < Effect from to ;
TUPLE: RecursiveCall < type-pred quot in out ;
TUPLE: RebuildEffect < InferEffect ;
TUPLE: ApplyEffects < chr-pred word tags in out ;
TUPLE: PerformCall < chr-pred call-pred effect-pred ;
TUPLE: EffectGen < chr-pred word in out body ;

! These can never be polymorphically different!
! TUPLE: Literal < chr-pred name quot ;

! Val stuff
TUPLE: Sum < val-pred x y ;
! TUPLE: Drop < chr-pred val ;
TUPLE: Dup < type-pred val copy ;

! This indicates that we can throw away all information about the variable,
! typically that happens if a literal gets inlined.
TUPLE: Dead < chr-pred val ;
! TUPLE: Use < val-pred ;

TUPLE: Lt < val-pred x ;
TUPLE: Le < val-pred x ;
TUPLE: Gt < val-pred x ;
TUPLE: Ge < val-pred x ;
TUPLE: Eq < val-pred x ;
TUPLE: Ne < val-pred x ;
UNION: comp-expr Lt Le Gt Ge Eq Ne ;
INSTANCE: comp-expr has-opposite
INSTANCE: comp-expr transitive
M: Lt opposite-pred drop Ge ;
M: Ge opposite-pred drop Lt ;
M: Gt opposite-pred drop Le ;
M: Le opposite-pred drop Gt ;
M: Eq opposite-pred drop Ne ;
M: Ne opposite-pred drop Eq ;

! Types with constructors.
! Those can appear in effects as syntactic matches
TUPLE: Tuple < type-pred ;
    ! Expressions.

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
! ** Value Predicates
! Redundancies
CHR: unique-type-preds @ AS: ?p <={ type-pred ?x . ?xs } // AS: ?q <={ type-pred ?x . ?xs } --
[ ?p ?q [ class-of ] same? ] | ;

! CHR: make-lit-val @ // { Is ?x A{ ?v } } -- | { Literal ?x ?v } ;

! Early drops
! CHR: drop-lit-type-preds @ { Drop ?x } { Literal ?x __ } // AS: ?p <={ type-pred } -- [ ?x ?p vars in? ] | ;
! CHR: drop-lit @ { Drop ?q } // { Literal ?q __ } -- | ;

! If we collected a value in a context, then in that context all predicates containing information about it
! would become universally qualified...

CHR: dead-type-preds @ { Dead ?x } // AS: ?p <={ type-pred } -- [ ?x ?p vars in? ] | ;
! CHR: simplify-dropped-choice { C ?c P{ Drop ?a } } { C ?d Is{  } }
CHR: drop-backwards-same-ctx @ { C ?c P{ Drop ?b } } // { C ?c Is{ ?b ?a } } -- | [ ?b ?a ==! ] ;
! CHR: drop-backwards @ // { Drop ?b } Is{ ?b ?a } -- | { Drop ?a } ;

CHR: unique-is @ // { Is ?x ?x } -- | ;


! CHR: same-is-def-must-be-same-var @ { C ?c Is{ ?x ?a } } // { C ?c Is{ ?x ?b } } -- [ ?a term-var? not ]
! [ ?b term-var? ] | [ ?x ?b ==! ] ;

! CHR: drop-dest-set-var @ { Drop ?y } // { Is ?y ?x } -- | [ ?x ?y ==! ] ;

! CHR: drop-lit-implies-used @ { Drop ?q } Is{ ?q A{ ?v } } // { Used ?x } -- | ;
! CHR: drop-lit-type-preds @ { Used ?x } { Is ?q A{ ?v } } // AS: ?p <={ type-pred } -- [ ?x ?p vars in? ] | ;
! CHR: drop-lit-val-preds-in-ctx @ { C ?c P{ Used ?x } } { C ?c Is{ ?q A{ ?v } }  } // { C ?c AS: ?p <={ type-pred } } -- [ ?x ?p vars in? ] | ;
! CHR: drop-lit-in-ctx @ // { C ?c P{ Drop ?q }  } { C ?d Is{ ?q A{ ?v } } } -- [ ?c ?d implies? ] | ;

! CHR: unique-use @ { Use ?x } // { Use ?x } -- | ;

! NOTE: This is the critical point about variable identity vs. value reference identity!
! CHR: redundant-is @ // { Is ?x ?x } -- | ;
! CHR: symbolic-eq-is-same @ { Is ?x ?y } // -- [ ?x term-var? ] [ ?y term-var? ] | [ ?x ?y ==! ] ;

CHR: destructure-stack-assignment-right @ // Is{ ?y L{ ?x . ?xs } } -- [ ?y term-var? ] |
[ ?y L{ ?a . ?b } ==! ]
{ Is ?a ?x }
{ Is ?b ?xs } ;

CHR: destructure-stack-assignment-left @ // Is{ L{ ?x . ?xs } ?y } -- [ ?y term-var? ] |
! [ L{ ?a . ?b } ?y ==! ]
[ ?y L{ ?a . ?b } ==! ]
{ Is ?x ?a }
{ Is ?xs ?b } ;

CHR: destructure-stack-assignment @ // Is{ L{ ?x . ?xs } L{ ?y . ?ys } } -- |
Is{ ?x ?y }
Is{ ?xs ?ys } ;

! Updating version when tracking dups
! CHR: is-transitive @ { Is ?b ?c } // { Is ?a ?b } -- | [ ?b ?a ==! ] ;
CHR: is-transitive-in-same-ctx @ { C ?x Is{ ?b ?a } } // { C ?x Is{ ?c ?b } } -- | [ ?c ?b ==! ] ;
CHR: is-transitive @ Is{ ?b ?a } // Is{ ?c ?b } -- | Is{ ?c ?a } ;

! NOTE: that one necessitates re-wrapping if we need an input-output interface with explicit different var-names.
CHR: is-same-var-in-top-ctx @ // { C f Is{ ?b ?c } } -- [ ?b term-var? ] [ ?c term-var? ] | [ ?b ?c ==! ] ;

! CHR: is-transitive @ Is{ ?b ?a } // Is{ ?c ?b } -- | [ ?b ?c ==! ] ;
! CHR: is-transitive-in-any-ctx @ Is{ ?c ?b } Is{ ?b ?a } // -- | Is{ ?c ?a } ;
! CHR: copy-trans-lit @ Is{ ?b A{ ?v } } // Is{ ?c ?b } -- | Is{ ?c ?v } { Used ?b } ;
! CHR: is-copies-literals @ Is{ ?x A{ ?v } } // Is{ ?y ?x } -- | Is{ ?y ?v } ;
! CHR: dup-copies-literals @ Is{ ?x A{ ?v } } // { Dup ?y ?x } -- | Is{ ?y ?v } ;

! CHR: use-cancels-dup-1 @ // { Dup ?x ?y } { Drop ?x } -- | [ ?x ?y ==! ] ;
! CHR: use-cancels-dup-2 @ // { Dup ?y ?x } { Drop ?x } -- | [ ?y ?x ==! ] ;

! CHR: dup-source @ { Dup ?b ?c } // { Is ?a ?b } -- | [ ?b ?a ==! ] ;

! TODO: same things backward if e.g. interval propagation turned out to know an exact value
! CHR: lit-trans-is-lit-forward @ { Literal ?x __ } // { Is ?x ?y } -- | [ ?y ?x ==! ] ;

CHR: trans-val-preds-backward @ <={ Is ?x ?y } AS: ?p <={ val-pred ?x . ?xs } // -- |
[ ?p clone ?y >>val ] ;

CHR: trans-val-preds-forward @ <={ Is ?y ?x } AS: ?p <={ val-pred ?x . ?xs } // -- |
[ ?p clone ?y >>val ] ;

CHR: dup-val-preds-backward @ <={ Dup ?x ?y } AS: ?p <={ val-pred ?x . ?xs } // -- |
[ ?p clone ?y >>val ] ;

CHR: dup-val-preds-forward @ <={ Dup ?y ?x } AS: ?p <={ val-pred ?x . ?xs } // -- |
[ ?p clone ?y >>val ] ;


! *** Move up expression definitions to the output-most variable
! CHR: transitive-expr @ Is{ ?c ?b } // { Expr ?b ?v } -- | { Expr ?c ?v } ;
! CHR: transitive-expr-same-context @ { C ?c Is{ ?c ?b } } // { C ?c P{ Expr ?b ?v } } -- | { C ?c P{ Expr ?c ?v } } ;


! ** Import type solvers
IMPORT: chr-types

! ** Some Conditional reasoning
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

! ** Relation completion
! CHR: also-opposite-rel @ AS: ?p <={ has-opposite ?x ?y } // -- |
! [ { ?y ?x } ?p opposite-pred slots>tuple ] ;

: make-opposite-pred ( pred -- pred )
    [ tuple-slots ] [ opposite-pred ] bi slots>tuple ;

CHR: Not>opposite-rel @ // AS: ?q Not{ ?p } -- [ ?p has-opposite? ] |
[ ?p make-opposite-pred ] ;

CHR: complete-neg-assumption @ // { --> ?c ?p } -- [ ?p has-opposite? ] |
[ ?p make-opposite-pred ?c swap \--> boa ] ;

! CHR: normalize-gt @ // { Gt ?x ?y } -- | { Le ?y ?x } ;

! CHR: transitive-rel @ AS: ?p <={ transitive ?x ?y } AS: ?q { transitive ?y ?z } // -- [ ?p ?q [ class-of ] same? ] |
! [ { ?x ?z } ?p class-of slots>tuple ] ;

CHR: propagate-transitive-pred-backward @ Is{ ?y ?x } // AS: ?p <={ transitive ?y ?z } -- |
[ { ?x ?z } ?p class-of slots>tuple ] ;
! CHR: propagate-comp-pred-forward @ Is{ ?y ?z } // AS: ?p <={ transitive ?x ?y } -- |
! [ { ?x ?z } ?p class-of tuple>slots ] ;
! CHR: propagate-transitive-pred-dup-lhs @ { Dup ?y ?x } AS: ?p <={ transitive ?x ?z } // -- |
! [ { ?y ?z } ?p class-of slots>tuple ] ;
CHR: propagate-transitive-pred-dup-rhs-1 @ { Dup ?z ?y } AS: ?p <={ transitive ?x ?y } // -- |
[ { ?x ?z } ?p class-of slots>tuple ] ;
CHR: propagate-transitive-pred-dup-rhs-2 @ { Dup ?y ?z } AS: ?p <={ transitive ?x ?y } // -- |
[ { ?x ?z } ?p class-of slots>tuple ] ;

! ** GC of used-up literals
! CHR: collect-dropped-literals { Literal }

! ** Include effect rebuilding

IMPORT: chr-effects

! ** Apply Effects at call sites
CHR: apply-call-effect @ Is{ ?b { call L{ ?q . ?a } } } AS: ?e P{ Effect ?q __ ?rho ?sig ?l } // --
[ ?e instantiate-effect :>> ?k ]
|
[ ?k constraints>> ]
[ ?k [ in>> ] [ out>> ] bi 2array { ?a ?b } ==! ] ;
! [ ?e instantiate-effect
!   [ constraints>> ]
!   bi 2array
! ] ;
! { ApplyEffect ?a ?b ?e } ;
! |
! [| | ?e instantiate-effect [ in>> ] [ out>> ] [ constraints>> ]
!  tri :> ( in out body )
!  { in out } { ?a ?b } solve-eq drop
!  {
!      Is{ in ?a }
!      Is{ ?b out }
!      body
!  }
! ] ;

! ** Domain-specific solver triggers
! Here be special per-word stuff

CHR: math-uses-numbers @ { Eval ?w L{ ?x ?y . __ } __ } // -- [ ?w math-generic? ] |
{ Instance ?x number }
{ Instance ?y number } ;

CHR: plus-is-sum @ { Eval + L{ ?x ?y . __ } L{ ?z . __ } } // -- |
{ Instance ?z number }
{ Sum ?x ?y ?z } ;


CONSTANT: rel-preds H{
    { > gt }
    { < lt }
    { >= ge }
    { <= le }
    { = eql }
}

CHR: comparison-defines-rel @ P{ Expr ?x { ?w ?a ?b } } // -- [ ?w rel-preds key? ] |
[ ?x { ?a ?b } ?w rel-preds at slots>tuple <--> boa ] ;

! CHR: not-Gt-pred @ { Not P{ Gt ?x ?y} } // -- | { le ?x ?y } ;
! CHR: not-Ge-pred @ { Not P{ Ge ?x ?y } } // -- | Not{  }

! CHR: gt-pred-comp @ { Gt ?x ?y } // -- | Not{ P{ le ?y ?x } } ;
! ! CHR: gt-pred-comp @ { Gt ?x ?y } // -- | { gt ?y ?x } ;
! CHR: ge-pred-comp @ { Ge ?x ?y } // -- | { le ?y ?x } ;
! CHR: lt-pred-comp @ { Lt ?x ?y } // -- | Not{ P{ le ?y ?x } } ;
! ! CHR: lt-pred-comp @ { Lt ?x ?y } // -- | { lt ?y ?x } ;
! CHR: le-pred-comp @ { Le ?x ?y } // -- | { le ?x ?y } ;



! ** Partial evaluation

IMPORT: chr-quot

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

: build-rules ( word/quot -- constraints )
    [ build-quot-expr quots swap run-chr-query store>> ] with-var-names ;
