USING: accessors arrays chr.factor chr.factor.effects chr.factor.intra-effect
chr.factor.phi chr.factor.word-types chr.parser chr.state kernel quotations
sequences sets terms ;

IN: chr.factor.composition


! * CHR Program for Composition solving
CHRAT: chr-comp { }

! ** Type Definitions
CHR: start-type-of @ // { InferType ?q } -- | { ?TypeOf ?q ?tau } ;

CHR: unique-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?tau } -- | ;

CHR: conflicting-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- [ ?tau full-type? ] [ ?sig full-type? ] | [ "conflicting type-defs" throw f ] ;

CHR: have-recursive-type @ // { Recursion ?x __ ?sig } { TypeOf ?x ?rho } { ?TypeOf ?x ?sig } -- |
[ ?sig ?rho ==! ] ;

! *** Deferred Inference

! These should become "active" as soon as the current inference is done
! Assumption: The hook is only activated if no inference is still active
! TODO: If we ever have recursive macro expansion, this must be verified to still
!  perform things in the expected order
CHR: infer-deferred-effect @ // { TypeOfDone } { ?DeferTypeOf ?p ?sig }  -- |
{ ?TypeOf ?p ?rho }
{ ReinferWith ?rho ?sig }
{ TypeOfDone } ;

! NOTE: assuming that we catch all dependent changes because we assume that all dependent
! changes reference the unknown type. I.e. it must not matter whether we expand the macro first and then
! compose types with the expansion, or we delay the expansion, compose with that delayed expansion and then
! substitute the expanded type.
! NOTE: inserting a re-try here because of nested expansion???
CHR: reinfer-deferred-type @ { ReinferWith ?e ?sig } // { TypeOf ?x ?tau } --
[ ?e full-type? ]
[ ?sig ?tau vars in? ]
[ ?tau { { ?sig ?e } } lift* :>> ?d ]
|
! TODO: check if we need fresh effects here.  If not, could use ComposeEffect directly
{ ComposeType ?d P{ Effect ?y ?y f f } ?rho }
{ TypeOf ?x ?rho }
    ;

! NOTE: re-inference does affect already present types.  To make sure all references to running inferences
! are caught, the type is substituted
CHR: did-reinfer-deferred-type @ // { ReinferWith ?e ?sig } -- [ ?e full-type? ] | [ ?sig ?e ==! ] ;


! *** Inference Step done

! find object fulfilling quot, if found, return with rest of sequence.  Otherwise
! return sequence unchanged and f.
: find-remove ( seq quot -- seq obj/f )
    dupd find
    [ [ swap remove-nth ] dip ] when* ; inline


! TODO: destructuring in a sequence match would be nice...
! Intercept effects that have embedded xors
! NOTE: it looks like we don't ever see them as reqular answered inference requests,
! As they occur during re-inference after substituting the lazy effect type...
! CHR: intercept-xor-call-effect-answer @ { TypeOf ?x P{ Effect ?a ?b ?l ?p } } // { ?TypeOf ?x ?sig } --
CHR: intercept-xor-call-effect-answer @ // { TypeOf ?x P{ Effect ?a ?b ?l ?p } } --
[ ?p [ CallXorEffect? ] find-remove swap :>> ?q drop :>> ?r ]
[ ?r

  [ type>> ]
  [ in>> ]
  [ out>> ]
   tri
  :>> ?o drop
  :>> ?i drop
  [ type2>> ]
  [ type1>> ] bi
  :>> ?c drop
  :>> ?d drop
  t
]
|
[| |
 ?a ?b ?l ?q { P{ Instance ?v ?c } P{ CallEffect ?v ?i ?o } } append Effect boa :> y
 ?a ?b ?l ?q { P{ Instance ?v ?d } P{ CallEffect ?v ?i ?o } } append Effect boa :> z

 P{ ComposeType y P{ Effect ?m ?m f f } ?rho }
 P{ ComposeType z P{ Effect ?n ?n f f } ?tau }
 2array
]
{ MakeXor ?rho ?tau ?sig }
{ CheckXor f ?sig ?s }
{ TypeOf ?x ?s } ;

! NOTE: this is the point where other depending inferences get assigned their missing type variable.  Any change to the existing type
! after that is not transported into the dependent inference.  So any stuff that must be changed before supplying the known type must be performed here
! BUT: Do we even have the macro type available already (in case of macros)

CHR: answer-type @ { TypeOf ?x ?tau } // { ?TypeOf ?x ?sig } -- [ ?tau full-type? ] | [ ?sig ?tau ==! ]
{ TypeOfDone } ;

CHR: double-word-inference-special @ { ?TypeOf [ ?x ] ?tau } // { ?TypeOf [ ?x ] ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ]
[ ?x callable-word? ] [ ?x rec-defaults :>> ?e ] |
[ ?sig ?e ==! ] ;

CHR: double-word-inference @ { ?TypeOf [ ?x ] ?tau } // { ?TypeOf [ ?x ] ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ]
[ ?x callable-word? ] |
[ ?sig P{ Effect ?a ?b f { { P{ CallRecursive ?x ?a ?b } } } } ==! ] ;

CHR: double-inference-queue @ { ?TypeOf ?x ?tau } { ?TypeOf ?x ?sig } // -- [ ?tau term-var? ] [ ?sig term-var? ] |
{ Recursion ?x ?tau ?sig } ;

CHR: check-word-fixpoint-type @ { TypeOfWord ?w ?rho } // -- [ ?rho full-type? ] |
{ CheckFixpoint ?w ?rho } ;
CHR: have-type-of-word-call @ { ?TypeOf [ ?w ] ?sig } { TypeOfWord ?w ?rho } // --
! [ ?rho valid-effect-type? ]
[ ?rho full-type? ]
[ ?w 1quotation :>> ?q ]
|
! ! NOTE: resolving recursive phi here with this if possible
! { ComposeType ?rho P{ Effect ?a ?a f f } ?tau }
! { TypeOf ?q ?tau } ;
{ TypeOf ?q ?rho } ;

IMPORT: chr-word-types

! * Intra-Effect Reasoning

IMPORT: chr-intra-effect

! * Intersection Type Composition

IMPORT: chr-phi

! * Effect Composition Reasoning

IMPORT: chr-effects


CHR: ask-type-of-word-call @ { ?TypeOf [ ?w ] ?tau } // -- [ ?w callable-word? ] [ ?tau term-var? ] |
{ TypeOfWord ?w ?sig } ;

CHR: compose-effects @ // { ComposeType P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } --
|
[| |
 P{ Effect ?a ?b ?x ?k } fresh-effect :> e1
 P{ Effect ?c ?d ?y ?l } fresh-effect :> e2
 ! P{ Effect ?a ?b ?k } fresh :> e1
 ! P{ Effect ?c ?d ?l } fresh :> e2
 P{ ComposeEffect e1 e2 ?tau }
] ;

CHR: compose-null-right @ // { ComposeType ?e null ?tau } -- |
[ ?tau null ==! ] ;

CHR: compose-null-left @ // { ComposeType null ?e ?tau } -- |
[ ?tau null ==! ] ;

CHR: compose-xor-effects-right @ // { ComposeType P{ Effect ?a ?b ?z ?k } P{ Xor ?x ?y } ?tau } -- |
{ ComposeType P{ Effect ?a ?b ?z ?k } ?x ?rho }
{ ComposeType P{ Effect ?a ?b ?z ?k } ?y ?sig }
{ MakeXor ?rho ?sig ?tau } ;

CHR: compose-xor-effects-left @ // { ComposeType P{ Xor ?x ?y } P{ Effect ?a ?b ?z ?k } ?tau } -- |
{ ComposeType ?x P{ Effect ?a ?b ?z ?k } ?rho }
{ ComposeType ?y P{ Effect ?a ?b ?z ?k } ?sig }
{ MakeXor ?rho ?sig ?tau } ;


CHR: compose-xor-effects-both @ // { ComposeType P{ Xor ?a ?b } P{ Xor ?c ?d } ?tau } -- |
{ ComposeType ?a P{ Xor ?c ?d } ?rho }
{ ComposeType ?b P{ Xor ?c ?d } ?sig }
{ MakeXor ?rho ?sig ?tau } ;


CHR: typeof-done-hook-finished @ // { TypeOfDone } -- | ;

;

: qt ( quot -- res )
    InferType boa 1array chr-comp swap [ run-chr-query store>> ] with-var-names ;
