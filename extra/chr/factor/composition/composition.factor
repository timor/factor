USING: accessors arrays assocs chr.factor chr.factor.effects
chr.factor.intra-effect chr.factor.intra-effect.primitives chr.factor.phi
chr.factor.util chr.factor.word-types chr.parser chr.state
combinators.short-circuit generic kernel quotations sequences sets terms words ;

IN: chr.factor.composition


! * CHR Program for Composition solving
CHRAT: chr-comp { }

! ** Safety Checks
! TODO remove once not needed safety check, seems to be quite expensive!
UNION: context-tag PhiDone PhiMode FinishEffect MakeEffect ;
CHR: catch-top-level-tag @ // <={ context-tag } -- [ get-context not ] | [ "pred not allowed in toplevel context" throw ] ;

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

CHR: no-nested-type-queries @ // { ?TypeOf ?x ?tau } -- [ get-context ] | [ "Type query in sub-context!" throw ] ;

CHR: unique-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?tau } -- | ;

: final-type? ( x -- ? ) { [ full-type? ] [ canonical? ] } 1&& ;

ERROR: conflicting-type-defs thing existing new ;
CHR: conflicting-type @ // { TypeOf ?x ?tau } { TypeOf ?x ?sig } --
[ ?tau full-type? ] [ ?sig full-type? ] |
[ ?x ?tau ?sig conflicting-type-defs ] ;

! FIXME TBR?
CHR: have-recursive-type @ // { Recursion ?x __ ?sig } { TypeOf ?x ?rho } { ?TypeOf ?x ?sig } -- | [ "have-recursive-type tbr" throw ]
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

! TODO: maybe remove answers that are non-canonical?
! Trying that...
! 3x benchmark [ lastfoo5-list ] tqt
! without rule: 6508 preds 13.2 - 14.9 sec

! with rule: 6629 preds 12.5 - 14.4 sec
! This rule or the aggressive one below is needed for recursion induced over proper quotations
CHR: answer-incomplete-type @ // { TypeOf ?x ?tau } { ?TypeOf ?x ?sig } --
[ ?tau full-type? ] [ ?tau canonical? not ] | [ ?sig ?tau ==! ] ;

CHR: answer-type @ { TypeOf ?x ?tau } // { ?TypeOf ?x ?sig } --
[ ?tau full-type? ] |
! [ "Answer Type: " write ?x . f ]
[ ?sig ?tau ==! ] ;

! ! ! NOTE: approach too aggressive?
! CHR: remove-cached-non-canonical-type @ // { TypeOf ?x ?tau } --
! [ ?tau full-type? ] [ ?tau canonical? not ] | ;



! These are used when recursive calls are made to some special words (length etc.) for which we have special
! predicates
! TODO: replace with lazy dispatch inference
! CHR: double-word-inference-special @ { ?TypeOf [ ?x ] ?tau } // { ?TypeOf [ ?x ] ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ]
! [ ?x callable-word? ] [ ?x rec-defaults fresh-effect :>> ?e ] |
! [ ?sig ?e ==! ] ;

! Generics will never get a recursive type, methods might, though
! CHR: recursive-generic-inference @ { ?TypeOf [ ?x ] ?tau } // { ?TypeOf [ ?x ] ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ]
! [ ?x generic? ] |
! { MakeGenericDispatch ?x P{ Effect ?a ?b f f } ?sig } ;

! This is where a recursion predicate is inserted
CHR: double-word-inference @ { ?TypeOf [ ?x ] M{ ?tau } } // { ?TypeOf [ ?x ] M{ ?sig } } --
[ ?x callable-word? ] |
[ ?sig P{ Effect ?a ?b f { P{ CallRecursive ?x ?a ?b } } } ==! ] ;

! Replacing with a version that discards one query and equates the variables, and continues destructuring.
! Should then stop when arriving at a word, where the recursion is then broken.
CHR: double-inference-queue @ // { ?TypeOf ?x M{ ?tau } } { ?TypeOf ?x M{ ?sig } } -- |
! CHR: double-inference-queue @ { ?TypeOf ?x ?tau } // { ?TypeOf ?x ?sig } -- [ ?tau term-var? ] [ ?sig term-var? ] |
! [ "tbr" throw ]
[ ?sig ?tau ==! ]
! ;
{ ?TypeOf ?x ?tau } ;
! { Recursion ?x ?tau ?sig } ;


! ** Recursion resolution
! Currently relying on eager progress to resolve to at least one singly recursive body.
! That does not seem to be enough for complex-enough cases involving recursing trough quotations.
! Trying to resolve these cases once known.  Question is whether that would subsume the existing approach?

! CHR: have-fixpoint-type @ { FixpointTypeOf ?w ?rho } // { FixpointTypeOf ?w ?tau } -- | [ ?rho ?tau ==! ] ;
CHR: duplicate-call-edges @ // { CallsRecursive ?w ?rho } { CallsRecursive ?w ?tau } -- | [ "duplicate call edge" throw ] ;
CHR: compute-call-edges @ { TypeOfWord ?w ?rho } // -- [ ?rho full-type? ] [ ?rho recursive-tags :>> ?t ] |
{ CallsRecursive ?w ?t } ;

CHR: resolved-all-recursions @ // { TypeOfWord ?w ?rho } { CallsRecursive ?w { } } --
[ ?rho full-type? ] |
{ ReinferEffect ?rho ?sig }
{ CheckXor ?w ?sig ?tau }
[ ?tau f lift canonical? [ { ?tau "assumed non-recursive not canonical after resolution!" } throw ] unless f ]
{ TypeOfWord ?w ?tau } ;

! ! NOTE: this is probably not needed if the other version is used
! ! VER1
! CHR: incomplete-mutrec-word-typequery @ { TypeOfWord ?w ?rho } // { ?TypeOf [ ?w ] ?tau } --
! [ ?rho full-type? ]
! [ ?w ?rho recursive-tags remove [ f ] when-empty ] |
! [ ?tau P{ Effect ?a ?b f { P{ CallRecursive ?w ?a ?b } } } ==! ] ;
! ! [ ?w null ?rho substitute-recursive-call :>> ?sig ]
! ! | [ ?tau ?sig ==! ] ;

! NOTE: Explicitly instantiating the base case in parallel here, otherwise it will not be
! kept as alternative!
CHR: resolve-single-recursion @ // { TypeOfWord ?w ?rho } { CallsRecursive ?w { ?w } } -- [ ?rho full-type? ]
| { CheckFixpoint ?w ?rho }
{ ReinferEffect ?rho ?sig }
{ CheckXor ?w ?sig ?tau }
[ ?tau f lift canonical? [ { ?tau "single recursive not canonical after resolution!" } throw ] unless f ]
{ TypeOfWord ?w ?tau } ;

! Version where we preclude a recursion to ourselves when providing as partial type
! VER2
CHR: have-incomplete-mutrec-word-typequery @ { TypeOfWord ?w ?rho } // { ?TypeOf [ ?w ] ?tau } --
[ ?rho full-type? ]
[ ?w ?rho recursive-tags remove [ f ] when-empty ]
[ ?w null ?rho substitute-recursive-call :>> ?sig ]
| [ ?tau ?sig ==! ] ;

! FIXME: possibly only works in conjunction with the above when removing typeofword pred there?
! We seem to at least need a call-recursive injection, too.  It looks like the rule above could actually be an
! optimization here!  Also, without chaining rules we will not find longer recursion chains correctly.
CHR: expand-incomple-mutrec-word @ { TypeOfWord ?w ?rho } { CallsRecursive ?w ?k } // { TypeOfWord ?v ?sig } { CallsRecursive ?v ?l } --
[ ?rho full-type? ] [ ?sig full-type? ] [ ?w ?l in? ] [ ?v ?k in? ]
[ ?w null ?rho substitute-recursive-call :>> ?tau ]
[ ?w ?tau ?sig substitute-recursive-call :>> ?z ] |
{ ReinferEffect ?z ?y }
{ CheckXor ?v ?y ?x }
{ TypeOfWord ?v ?x } ;

CHR: elim-mutual-recursion-dependency @ { TypeOfWord ?v ?rho } { TypeOfWord ?w ?sig } // { CallsRecursive ?w ?l } --
[ ?rho full-type? ] [ ?rho canonical? ] [ ?v ?l in? ] [ ?v ?l remove :>> ?k ] |
{ CallsRecursive ?w ?k } ;

! ** Call types from word types

! This is here because there could be a dispatch expansion hidden, which we don't perform in the word type itself
CHR: have-type-of-generic-word-call @ { ?TypeOf [ ?w ] ?sig } { TypeOfWord ?w ?rho } // --
[ ?w generic? ]
[ ?rho canonical? ] |
{ ReinferEffect ?rho ?z }
{ CheckXor ?q ?z ?tau }
{ TypeOf [ ?w ] ?tau } ;

! TODO: Could do the input/output class handling here!
CHR: have-type-of-word-call @ { ?TypeOf [ ?w ] ?sig } { TypeOfWord ?w ?rho } // --
[ ?w generic? not ]
[ ?rho canonical? ]
| { TypeOf [ ?w ] ?rho } ;

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

! Interactive short cut
: qt ( quot -- res )
    InferType boa 1array chr-comp swap [ run-chr-query store>> ] with-var-names ;

! helper, really
: pick-type ( solution word -- type )
    swap values [ TypeOf? ] filter
    [ key>> = ] with find nip
    dup [ type>> ] when ;

GENERIC: get-type ( quot -- type )

M: callable get-type
    [ qt values [ TypeOf? ] filter ]
    [ [ swap key>> = ] curry find nip ] bi
    dup [ type>> ] when ;
M: word get-type
    1quotation get-type ;
