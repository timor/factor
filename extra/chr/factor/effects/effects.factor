USING: accessors arrays assocs chr.factor chr.parser chr.state
combinators.short-circuit kernel lists sequences sets terms types.util ;

IN: chr.factor.effects


! * Effect composition
! Responsible for actually triggering composing effect types and
! collecting results of inner predicate reasoning

CHRAT: chr-effects { }

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
CHR: inference-collision-2 @ AS: ?a <={ FinishEffect } AS: ?b <={ FinishEffect } // -- | [ ?a ?b nested-inference ] ;

! NOTE: assumed renaming here already
! NOTE: we have to generate object instance predicates for all values that may be generated using unification for each branch if missing!
CHR: rebuild-phi-effect @ { PhiMode } // { CheckPhiStack { ?a ?b } { ?c ?d } t } { ComposeEffect P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } --
|
[ { ?a ?b } { ?c ?d } ==! ]
{ MakeEffect ?a ?b f f ?tau }
{ Params ?x }
{ Params ?y }
[ ?k ?a ?ground-value ?b ?ground-value default-class-preds ]
[ ?l ?c ?ground-value ?d ?ground-value default-class-preds ]
[ ?k ]
[ ?l ]
{ FinishEffect ?tau }
    ;

CHR: dont-rebuild-non-phiable-effect @ // { PhiMode } { CheckPhiStack { ?a ?b } { ?c ?d } f } { ComposeEffect P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } -- |
[ ?tau null ==! ]
{ PhiDone } ;

! non-phi case
CHR: rebuild-compose-effect @ // { ComposeEffect P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } -- |
[ ?b ?c ==! ]
! NOTE: This happens if we have pre-defined effects but no known body yet (e.g. recursive calls)
! [ ?k dup term-var? [ drop f ] when ]
! [ ?l dup term-var? [ drop f ] when ]
{ MakeEffect ?a ?d f f ?tau }
{ Params ?x }
{ Params ?y }
[ ?k ]
[ ?l ]
{ FinishEffect ?tau } ;

! TODO: document this
CHR: force-union @ { PhiMode } { FixpointMode } // { Invalid } -- | ;

! * Post-Reasoning

! *** Phi Mode
! CHR: discard-non-union-pred @ { PhiMode } <={ MakeEffect } // <={ body-pred } -- | ;
! CHR: discard-leftover-binds @ { PhiMode } <={ MakeEffect } // <={ Bind } -- | ;
! CHR: phi-discard-leftover-params @ { PhiMode } <={ MakeEffect } // <={ Param } -- | ;
! CHR: phi-discard-phi-defs @ { PhiMode } <={ MakeEffect } // <={ Phi } -- | ;

CHR: collect-union-pred @ { PhiMode } { FinishEffect ?tau } // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } { Keep ?p } -- [ ?p live-vars ?e make-effect-vars intersects? ]
[ ?p ?l in? not ]
[ ?l ?p suffix :>> ?k ]
|
[| | ?p defines-vars ?x union :> y
 { MakeEffect ?a ?b y ?k ?tau } ] ;


CHR: phi-discard-discriminators @ { FinishEffect ?tau } { PhiMode } { MakeEffect __ __ __ __ ?tau } // <={ Discriminator } -- | ;
CHR: phi-discard-leftover-preds @ { FinishEffect ?tau } { PhiMode } { MakeEffect __ __ __ __ ?tau } // <={ body-pred } -- | ;
! TODO: not 100% sure the following isn't working too eagerly...
CHR: phi-discard-keeps @ { FinishEffect ?tau } { PhiMode } { MakeEffect __ __ __ __ ?tau } // <={ Keep } -- | ;

! *** Composition Mode
! These are live after the pred has been taken into account

! CHR: collect-call-recursive-input @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallRecursive ?m ?rho ?sig } --
! [ ?rho vars ?e make-effect-vars subset? ]
! [ ?x ?sig vars union :>> ?y ]
! [ ?l ?p suffix :>> ?k ]
! | { MakeEffect ?a ?b ?y ?k ?tau } ;

! NOTE: The only time for now where this was needed instead of the one above was for [ t ] loop...
CHR: collect-call-recursive @ { FinishEffect ?tau } // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallRecursive ?m ?rho ?sig } --
[ ?rho vars ?sig vars union ?e make-effect-vars intersects? ]
[ ?x ?rho vars union ?sig vars union :>> ?y ]
[ ?l ?p suffix :>> ?k ]
| { MakeEffect ?a ?b ?y ?k ?tau } ;

! *** All other preds
! CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p vars ?e make-effect-vars intersects? ]
! CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p live-vars ?e make-effect-vars subset? ]
CHR: collect-body-pred @ { FinishEffect ?tau } // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p live-vars ?e make-effect-vars intersects? ]
[ ?p ?l in? not ]
[ ?l ?p suffix :>> ?k ]
|
[| | ?p defines-vars ?x union :> y
 { MakeEffect ?a ?b y ?k ?tau } ] ;

CHR: collect-boa @ { FinishEffect ?tau } // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ Boa ?c ?i ?o } --
! [ ?i ?o [ vars ?e make-effect-vars in? ] bi@ or ]
[ ?p vars ?e make-effect-vars intersects? ]
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


! *** Sanity check
! CHR: must-cleanup @ { MakeEffect __ __ __ __ __ } AS: ?p <={ body-pred } // -- | [ ?p "leftovers" 2array throw f ] ;

! *** Discard unrelated predicates
CHR: cleanup-incomplete @ { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } // AS: ?p <={ body-pred } -- | ;

! This is triggered if phi mode is aborted
CHR: finish-disjoint-effect @ { PhiMode } { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } // { Params __ } { Invalid } -- |
[ ?tau null ==! ] ;

! This is triggered if composition modes determines the effect will terminate
CHR: finish-invalid-effect @ { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } // { Params __ } { Invalid } -- |
[ ?tau P{ Effect ?a ?b f { P{ Invalid } } } ==! ] ;

CHR: finish-valid-effect @ { FinishEffect ?tau } AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } // { Params __ } -- [ ?tau term-var? ]
[ ?x ?a vars diff ?b vars diff
  ! FIXME: this exposes what seems to be a bug in the term solver, probably something going wrong when f is assigned to a binding,
  ! resulting in a recursive-term-error in case for checking strange stuff...
  dup empty? [ drop f ] when
  :>> ?y drop t ]
|
[ ?tau P{ Effect ?a ?b ?y ?l } ==! ] ;

! NOTE: re-inserting the FinishEffect Predicates because they don't get reactivated by substitution
CHR: finish-phi-reasoning @ // { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } { PhiMode } -- [ ?tau term-var? not ] | { FinishEffect ?tau } { PhiDone } ;
CHR: finish-compositional-reasoning @ // { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } -- [ ?tau term-var? not ] | { FinishEffect ?tau } ;

! * Deferred inference requests

! Collect Effects to re-infer after deferred type has been determined
! CHR: make-reinfer-list @ { TypeOf ?x ?tau } { ReinferWith ?sig } // -- [ ?sig term-var? ] [ ?sig ?tau vars in? ] |
! { ReinferWhenKnown ?x ?sig } ;

! CHR: finish-make-reinfer-list @ // { ReinferWith ?sig } -- | ;

! CHR: reinfer-because-known @ // { FinishEffect ?y } { TypeOf ?x ?tau } { ReinferWhenKnown ?x ?sig } -- [ ?sig term-var? not ] [ ?y term-var? not ] |
! { ComposeType ?tau P{ Effect ?a ?a f f } ?rho }
! { TypeOf ?x ?rho }
! { FinishEffect ?y } ;

! These should become "active" as soon as the current inference is done
CHR: infer-deferred-effect @ // { ?DeferTypeOf ?p ?sig } { FinishEffect ?tau } -- [ ?tau term-var? not ] |
{ ?TypeOf ?p ?rho }
{ ReinferWith ?rho ?sig }
{ FinishEffect ?tau } ;

! * Token removal
CHR: finish-effect-done @ // { FinishEffect ?tau } -- [ ?tau term-var? not ] | ;

;
