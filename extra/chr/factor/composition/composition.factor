USING: accessors arrays assocs chr.factor chr.factor.intra-effect chr.factor.phi
chr.factor.word-types chr.parser chr.state combinators.short-circuit kernel
lists quotations sequences sets terms types.util ;

IN: chr.factor.composition


! * CHR Program for Composition solving
CHRAT: chr-comp { }

! ** Type Definitions
CHR: start-type-of @ // { InferType ?q } -- | { ?TypeOf ?q ?tau } ;

CHR: unique-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?tau } -- | ;

CHR: conflicting-type @ { TypeOf ?x ?tau } // { TypeOf ?x ?sig } -- [ ?tau full-type? ] [ ?sig full-type? ] | [ "conflicting type-defs" throw f ] ;

CHR: have-recursive-type @ // { Recursion ?x __ ?sig } { TypeOf ?x ?rho } { ?TypeOf ?x ?sig } -- |
[ ?sig ?rho ==! ] ;

CHR: answer-type @ { TypeOf ?x ?tau } // { ?TypeOf ?x ?sig } -- [ ?tau full-type? ] | [ ?sig ?tau ==! ] ;

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


IMPORT: chr-phi

! * Start Composition Reasoning
! ** Unification reasoning
: phi-stacks-unique? ( mapping -- ? )
    [ values [ dup list?
               ! Note: not testing the cdrs...
               [ list>array* ]
               [ 1array ] if
             ] map concat all-unique? ]
    [ f ] if* ;

CHR: rebuild-phi-check-stack @ { PhiMode } { ComposeEffect P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } // -- |
{ CheckPhiStack { ?a ?b } { ?c ?d } ?u } ;

! This check makes sure we don't run into endless stack balancing cases due to
! mismatched stack depths of branches, Also, we don't construct union branches
! if there is no unique phi mapping.  In that case, one branch is hiding
! equality constraints that the other one does not have
CHR: do-check-phi-stack @ // { CheckPhiStack ?i ?o ?u } -- [ ?u term-var? ] [ ?i ?o unify phi-stacks-unique? :>> ?w drop t ] |
{ CheckPhiStack ?i ?o ?w } ;

: default-class-preds ( preds in out -- preds )
    [ list>array* ] bi@ union
    [| preds var | preds [ { [ Instance? ] [ val>> var == ] } 1&& ] find nip
     [ f ] [ P{ Instance var object } ] if
    ] with map sift ;

ERROR: nested-inference a b ;
CHR: inference-collision @ AS: ?a <={ MakeEffect } AS: ?b <={ MakeEffect } // -- | [ ?a ?b nested-inference ] ;

! NOTE: assumed renaming here already
! NOTE: we have to generate object instance predicates for all values that may be generated using unification for each branch if missing!
CHR: rebuild-phi-effect @ { PhiMode } // { CheckPhiStack { ?a ?b } { ?c ?d } t } { ComposeEffect P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } --
|
[ { ?a ?b } { ?c ?d } ==! ]
{ Params ?x }
{ Params ?y }
[ ?k ?a ?ground-value ?b ?ground-value default-class-preds ]
[ ?l ?c ?ground-value ?d ?ground-value default-class-preds ]
[ ?k ]
[ ?l ]
{ MakeEffect ?a ?b f f ?tau } ;

CHR: dont-rebuild-non-phiable-effect @ // { PhiMode } { CheckPhiStack { ?a ?b } { ?c ?d } f } { ComposeEffect P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } -- |
[ ?tau null ==! ]
{ PhiDone } ;

! non-phi case
CHR: rebuild-compose-effect @ // { ComposeEffect P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } -- |
[ ?b ?c ==! ]
! NOTE: This happens if we have pre-defined effects but no known body yet (e.g. recursive calls)
! [ ?k dup term-var? [ drop f ] when ]
! [ ?l dup term-var? [ drop f ] when ]
{ Params ?x }
{ Params ?y }
[ ?k ]
[ ?l ]
{ MakeEffect ?a ?d f f ?tau } ;

! TODO: document this
CHR: force-union @ { PhiMode } { FixpointMode } // { Invalid } -- | ;

! * Intra-Effect Reasoning

! TODO: move up, or move answer trigger down
IMPORT: chr-intra-effect

! * Post-Reasoning

! *** Phi Mode
! CHR: discard-non-union-pred @ { PhiMode } <={ MakeEffect } // <={ body-pred } -- | ;
! CHR: discard-leftover-binds @ { PhiMode } <={ MakeEffect } // <={ Bind } -- | ;
! CHR: phi-discard-leftover-params @ { PhiMode } <={ MakeEffect } // <={ Param } -- | ;
! CHR: phi-discard-phi-defs @ { PhiMode } <={ MakeEffect } // <={ Phi } -- | ;

CHR: collect-union-pred @ { PhiMode } // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } { Keep ?p } -- [ ?p live-vars ?e effect-vars intersects? ]
[ ?p ?l in? not ]
[ ?l ?p suffix :>> ?k ]
|
[| | ?p defines-vars ?x union :> y
 { MakeEffect ?a ?b y ?k ?tau } ] ;


CHR: phi-discard-discriminators @ { PhiMode } <={ MakeEffect } // <={ Discriminator } -- | ;
CHR: phi-discard-leftover-preds @ { PhiMode } <={ MakeEffect } // <={ body-pred } -- | ;
! TODO: not 100% sure the following isn't working too eagerly...
CHR: phi-discard-keeps @ { PhiMode } <={ MakeEffect } // <={ Keep } -- | ;

! *** Composition Mode
! These are live after the pred has been taken into account

! CHR: collect-call-recursive-input @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallRecursive ?m ?rho ?sig } --
! [ ?rho vars ?e effect-vars subset? ]
! [ ?x ?sig vars union :>> ?y ]
! [ ?l ?p suffix :>> ?k ]
! | { MakeEffect ?a ?b ?y ?k ?tau } ;

! NOTE: The only time for now where this was needed instead of the one above was for [ t ] loop...
CHR: collect-call-recursive @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallRecursive ?m ?rho ?sig } --
[ ?rho vars ?sig vars union ?e effect-vars intersects? ]
[ ?x ?rho vars union ?sig vars union :>> ?y ]
[ ?l ?p suffix :>> ?k ]
| { MakeEffect ?a ?b ?y ?k ?tau } ;

! *** All other preds
! CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p vars ?e effect-vars intersects? ]
! CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p live-vars ?e effect-vars subset? ]
CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p live-vars ?e effect-vars intersects? ]
[ ?p ?l in? not ]
[ ?l ?p suffix :>> ?k ]
|
[| | ?p defines-vars ?x union :> y
 { MakeEffect ?a ?b y ?k ?tau } ] ;

CHR: collect-boa @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ Boa ?c ?i ?o } --
! [ ?i ?o [ vars ?e effect-vars in? ] bi@ or ]
[ ?p vars ?e effect-vars intersects? ]
[ ?l ?p suffix :>> ?k ]
[ ?x ?p vars union :>> ?y ] |
{ MakeEffect ?a ?b ?y ?k ?tau } ;

! TODO: abstract this shit...

! This will catch [ [ some-generic-word ] call ] inferences
! CHR: catch-xor-effect @ // { MakeEffect ?a ?b f f ?tau } { Literal ?q } { Instance ?q P{ Xor ?x ?y } } { CallEffect ?q ?a ?b } --
! [ ?a term-var? ] [ ?b term-var? ] |
! [ ?tau P{ Xor ?x ?y } ==! ] ;

! TODO: check whether this is even applicable...
! CHR: catch-unit-effect-call @ // { MakeEffect ?a ?b f f ?tau } { Literal ?q } { Instance ?q ?rho } { CallEffect ?q ?a ?b } --
! [ ?rho term-var? not ]
! [ ?a term-var? ] [ ?b term-var? ] |
! [ ?tau ?rho ==! ] ;


! TODO: pretty sure this needs to be moved up...
CHR: conflicting-makes @ { MakeEffect __ __ __ __ __ } { MakeEffect __ __ __ __ __ } // -- | [ "recursive-make" throw f ] ;

! *** Sanity check
! CHR: must-cleanup @ { MakeEffect __ __ __ __ __ } AS: ?p <={ body-pred } // -- | [ ?p "leftovers" 2array throw f ] ;
CHR: cleanup-incomplete @ { MakeEffect __ __ __ __ __ } // AS: ?p <={ body-pred } -- | ;

! This is triggered if phi mode is aborted
CHR: finish-disjoint-effect @ { PhiMode } { MakeEffect __ __ __ __ ?tau } // { Params __ } { Invalid } -- |
[ ?tau null ==! ] ;

! This is triggered if composition modes determines the effect will terminate
CHR: finish-invalid-effect @ { MakeEffect __ __ __ __ ?tau } // { Params __ } { Invalid } -- |
[ ?tau P{ Effect ?a ?b f { P{ Invalid } } } ==! ] ;

CHR: finish-valid-effect @ AS: ?e P{ MakeEffect ?a ?b __ ?l ?tau } // { Params ?x } -- [ ?tau term-var? ]
[ ?x ?e effect-vars intersect
  ! FIXME: this exposes what seems to be a bug in the term solver, probably something going wrong when f is assigned to a binding,
  ! resulting in a recursive-term-error in case for checking strange stuff...
  dup empty? [ drop f ] when
  :>> ?y drop t ]
|
[ ?tau P{ Effect ?a ?b ?y ?l } ==! ] ;

CHR: finish-phi-reasoning @ // { MakeEffect __ __ __ __ ?tau } { PhiMode } -- [ ?tau term-var? not ] | { PhiDone } ;
CHR: finish-compositional-reasoning @ // { MakeEffect __ __ __ __ ?tau } -- [ ?tau term-var? not ] | ;

;

: qt ( quot -- res )
    InferType boa 1array chr-comp swap [ run-chr-query store>> ] with-var-names ;
