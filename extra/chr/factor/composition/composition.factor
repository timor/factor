USING: accessors arrays chr.factor chr.factor.effects chr.factor.intra-effect
chr.factor.intra-effect.primitives chr.factor.phi chr.factor.word-types
chr.parser chr.state generic kernel quotations terms ;

IN: chr.factor.composition


! * CHR Program for Composition solving
CHRAT: chr-comp { }

! ** Debug Helpers
! CHR: print-ask-type @ { ?TypeOf ?q ?tau } // -- |
! [ "Ask type: " write ?q . flush f ] ;

! CHR: print-have-type @ { TypeOf ?q ?tau } // -- [ ?tau full-type? ] |
! [ "Have full type: " write ?q . "as" print ?tau . flush f ] ;

! CHR: print-have-word-type @ { TypeOfWord ?q ?tau } // -- [ ?tau full-type? ] |
! [ "Have full word type: " write ?q . "as" print ?tau . flush f ] ;

! CHR: print-ask-recursion-type @ { ?TypeOf [ ?x ] ?tau } { ?TypeOf [ ?x ] ?sig } // -- [ ?tau term-var? ] [ ?sig term-var? ]
! [ ?x callable-word? ]
! |
! [ "Recursive Inference of " write ?x . flush f ] ;

! CHR: print-ask-deferred-type @ { ?DeferTypeOf ?q ?tau } // -- |
! [ "Perform Deferred Inference of " write ?q . flush f ] ;

! ** Type Definitions
CHR: start-type-of @ // { InferType ?q } -- | { ?TypeOf ?q ?tau } ;

CHR: unique-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?tau } -- | ;

ERROR: conflicting-type-defs thing existing new ;
CHR: conflicting-type @ { TypeOf ?x ?tau } { TypeOf ?x ?sig } // -- |
[ ?x ?tau ?sig conflicting-type-defs ] ;

CHR: have-recursive-type @ // { Recursion ?x __ ?sig } { TypeOf ?x ?rho } { ?TypeOf ?x ?sig } -- |
[ ?sig ?rho ==! ] ;

! *** Deferred Inference

! Short circuit already known type
CHR: deferred-effect-already-known @ { TypeOf ?x ?tau } // { ?DeferTypeOf ?x ?sig } -- [ ?tau full-type? ] |
[ ?sig ?tau ==! ] ;

! TODO: check
! FIXME: more like an error if that happens...
CHR: request-same-deferred-type @ { ?DeferTypeOf ?x ?sig } // { ?DeferTypeOf ?x ?tau } -- [ ?sig term-var? ] [ ?tau term-var? ] |
[ ?sig ?tau ==! ] ;

! *** Inference Step done

! NOTE: this is the point where other depending inferences get assigned their missing type variable.  Any change to the existing type
! after that is not transported into the dependent inference.  So any stuff that must be changed before supplying the known type must be performed here
! BUT: Do we even have the macro type available already (in case of macros)

CHR: answer-type @ { TypeOf ?x ?tau } // { ?TypeOf ?x ?sig } -- [ ?tau full-type? ] |
! [ "Answer Type: " write ?x . f ]
[ ?sig ?tau ==! ] ;

! These are used when recursive calls are made to some special words (length etc.) for which we have special
! predicates
! TODO: replace with lazy dispatch inference
! CHR: double-word-inference-special @ { ?TypeOf [ ?x ] ?tau } // { ?TypeOf [ ?x ] ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ]
! [ ?x callable-word? ] [ ?x rec-defaults fresh-effect :>> ?e ] |
! [ ?sig ?e ==! ] ;

! Generics will never get a recursive type, methods might, though
CHR: recursive-generic-inference @ { ?TypeOf [ ?x ] ?tau } // { ?TypeOf [ ?x ] ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ]
[ ?x generic? ] |
{ MakeGenericDispatch ?x P{ Effect ?a ?b f f } ?sig } ;

! This is where a recursion predicate is inserted
CHR: double-word-inference @ { ?TypeOf [ ?x ] ?tau } // { ?TypeOf [ ?x ] ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ]
[ ?x callable-word? ] |
[ ?sig P{ Effect ?a ?b f { P{ CallRecursive ?x ?a ?b } } } ==! ] ;
! [ ?sig P{ Effect ?a ?b { ?r } { { P{ EnterRecursive ?x ?a ?r } P{ CallRecursive ?x ?r ?b } } } } ==! ] ;

! FIXME: This doesn't seem to work correctly...
! CHR: double-inference-queue @ { ?TypeOf ?x ?tau } { ?TypeOf ?x ?sig } // -- [ ?tau term-var? ] [ ?sig term-var? ] |
! { Recursion ?x ?tau ?sig } ;

! Replacing with a version that discards one query and equates the variables, and continues destructuring.
! Should then stop when arriving at a word, where the recursion is then broken.
CHR: double-inference-queue @ // { ?TypeOf ?x ?tau } { ?TypeOf ?x ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ] |
[ ?sig ?tau ==! ]
{ ?TypeOf ?x ?tau } ;
! { Recursion ?x ?tau ?sig } ;

CHR: check-word-fixpoint-type @ { TypeOfWord ?w ?rho } // -- [ ?rho full-type? ] |
{ CheckFixpoint ?w ?rho } ;

! NOTE: Rebuilding an annotated effect here.  This could still be not correct because there are cached
! types of quotations that have been inferred for the recursive word itself, which don't appear in a wrapped
! context?
! TODO maybe instantiate the tag? Probably not needed.
! NOTE: relying on known effect for the fixpoint type for now to derive the stack effect, which is not ideal
CHR: have-type-of-recursive-word-call @ { ?TypeOf [ ?w ] ?sig } { TypeOfWord ?w ?rho }
{ FixpointTypeOf ?w P{ Effect ?r ?s ?l ?p } }
{ RecursionTypeOf ?w ?tau } // --
[ ?rho full-type? ]
[ ?tau full-type? ]
[ ?w 1quotation :>> ?q ] |
[ ?r fresh ?a ==! ]
[ ?s fresh ?b ==! ]
{ ReinferEffect P{ Effect ?a ?b f { P{ CallRecursive ?w ?a ?b } } } ?y }
{ CheckXor ?w P{ Xor
                 ?y
                 P{ Effect ?r ?s ?l ?p } }
  ?z }
{ TypeOf ?q ?z } ;


! This is here because there could be a dispatch expansion hidden, which we don't perform in the word type itself
CHR: have-type-of-generic-word-call @ { ?TypeOf [ ?w ] ?sig } { TypeOfWord ?w ?rho } // --
[ ?w generic? ]
[ ?rho full-type? ]
[ ?w 1quotation :>> ?q ]
|
{ ReinferEffect ?rho ?z }
{ CheckXor ?q ?z ?tau }
{ TypeOf ?q ?tau } ;

! TODO: Could do the input/output class handling here!
CHR: have-type-of-word-call @ { ?TypeOf [ ?w ] ?sig } { TypeOfWord ?w ?rho } // --
! [ ?rho valid-effect-type? ]
[ ?w generic? not ]
[ ?rho full-type? ]
[ ?w 1quotation :>> ?q ]
| { TypeOf ?q ?rho } ;

IMPORT: chr-word-types

! * Primitive Expansion
IMPORT: chr-factor-prim

! * Intra-Effect Reasoning

IMPORT: chr-intra-effect

! * Intersection Type Composition

IMPORT: chr-phi

! * Effect Composition Reasoning

IMPORT: chr-effects


! Default position where [ foo ] queries are converted to TypeOfWord foo preds.
CHR: ask-type-of-word-call @ { ?TypeOf [ ?w ] ?tau } // -- [ ?w callable-word? ] [ ?tau term-var? ] |
{ TypeOfWord ?w ?sig } ;

CHR: compose-trivial-left @ // { ComposeType P{ Effect ?a ?a f f } ?y ?tau } -- |
[ ?tau ?y ==! ] ;
CHR: compose-trivial-right @ // { ComposeType ?x P{ Effect ?a ?a f f } ?tau } -- |
[ ?tau ?x ==! ] ;

CHR: compose-effects @ // { ComposeType P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } --
|
[| |
 P{ Effect ?a ?b ?x ?k } fresh-effect :> e1
 P{ Effect ?c ?d ?y ?l } fresh-effect :> e2
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

;

: qt ( quot -- res )
    InferType boa 1array chr-comp swap [ run-chr-query store>> ] with-var-names ;
