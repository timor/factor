USING: accessors arrays assocs chr.factor chr.factor.intra-effect.liveness
chr.factor.util chr.parser chr.state combinators.short-circuit kernel lists
sequences sets terms types.util ;

IN: chr.factor.effects


! * Effect composition
! Responsible for actually triggering composing effect types and
! collecting results of inner predicate reasoning

CHRAT: chr-effects { }

! ** Unification reasoning
! TODO: move that stuff over to phi!
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
CHR: inference-collision @ AS: ?a P{ MakeEffect __ __ __ __ __ } AS: ?b P{ MakeEffect __ __ __ __ __ } // -- | [ ?a ?b nested-inference ] ;
! CHR: inference-collision-2 @ AS: ?a <={ FinishEffect } AS: ?b <={ FinishEffect } // -- | [ ?a ?b nested-inference ] ;

! NOTE: assumed renaming here already
! NOTE: we have to generate object instance predicates for all values that may be generated using unification for each branch if missing!
CHR: rebuild-phi-effect @ // { PhiMode } { CheckPhiStack { ?a ?b } { ?c ?d } t } { ComposeEffect P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } --
|
[ { ?a ?b } { ?c ?d } ==! ]
! { Params ?x }
! { Params ?y }
{ MakeEffect ?a ?b f f ?tau }
[ ?k ?a ?ground-value ?b ?ground-value default-class-preds ]
[ ?l ?c ?ground-value ?d ?ground-value default-class-preds ]
[ ?k ]
[ ?l ]
{ PhiMode }
{ FinishEffect ?tau }
    ;

CHR: dont-rebuild-non-phiable-effect @ // { PhiMode } { CheckPhiStack { ?a ?b } { ?c ?d } f } { ComposeEffect P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } -- |
[ ?tau null ==! ]
{ PhiDone } ;

! FIXME This is soooooooo slow, need better alternative
! Trying to fix this now...
IMPORT: chr-factor-liveness

:: make-spool ( target variables preds -- spool )
    preds
    ! variables [ Roots boa ] [ Live boa ] bi [ suffix ] bi@
    >list :> body
    P{ Spool target body } ;

! non-phi case
CHR: rebuild-compose-effect @ // { ComposeEffect P{ Effect ?a ?b ?x ?k } P{ Effect ?c ?d ?y ?l } ?tau } -- |
[ ?b ?c ==! ]
! FIXME: context scoping!
[ "comp" [
      { MakeEffect ?a ?d f f ?tau }
      P{ CompMode }
      ?tau
      ?a vars ?d vars union
      ! TODO: maybe sort or adjust order to force early mismatches?
      ! XXX: this could also be important because of relying on stop conditions here!
      ! At least for CallXors, or later-known call-recursives? Ideally only for callxors!
      ?k ?l append
      make-spool
      3array
  ] new-context ] ;
! [
!     ?k ?l 2merge
!     ?i vars [ Roots boa ] [ Live boa ] bi [ suffix ] bi@
!     >list :>> ?p drop t ]
! |
! [ ?b ?c ==! ]
! ! NOTE: This happens if we have pre-defined effects but no known body yet (e.g. recursive calls)
! ! [ ?k dup term-var? [ drop f ] when ]
! ! [ ?l dup term-var? [ drop f ] when ]
! ! { CompMode }
! { MakeEffect ?a ?d f f ?tau }
! { Spool ?tau ?p }
! ! [ ?k ]
! ! [ ?l ]
! ! { Roots ?i }
! ! { Live ?i }
! [ ?i vars [ Roots boa ] [ Live boa ] bi 2array ]
! ! { FinishEffect ?tau }
!     ;

CHR: interrupt-spool @ { Invalid } // { Spool ?tau L{ ?x . __ } } -- | { Spool ?tau L{ } } ;
! This is triggered at least by macro expansion, which must always succeed
! in a nested inference manner.
CHR: throw-type-query @ // { Spool ?tau L{ } } { ?DeferTypeOf ?q M{ ?sig } } -- |
[ [ P{ ?TypeOf ?q ?sig } ] no-context ] { Spool ?tau L{ } } ;
! [ P{ FinishEffect ?tau } ] ;

CHR: end-spool @ { MakeEffect ?i ?o __ __ __ } // { Spool ?tau L{ } } --
! [ ?i value-vars :>> ?a ] [ ?o value-vars :>> ?b ]
[ ?i vars :>> ?a ] [ ?o vars :>> ?b ]
[ ?a ?b union :>> ?c ]
|
! { FinishEffect ?tau }
! { Live ?c }
! { Left ?a } { Right ?b }
! { Scope ?i ?o }
! { Given ?a } { Define ?b }
{ Live ?c } { Def ?a } { Use ?b }
{ FinishEffect ?tau } ;
CHR: spool-one-pred @ // { Spool ?tau L{ ?x . ?xs } } -- | [ ?x ] { Spool ?tau ?xs } ;

! Body-only reinference requests, usually because some body preds have been changed lazily
! FIXME: ordering might need to be adjusted here to account for mutual recursion branch elimination!
! FIXME: a checkxor might be needed as well? Currently these are done explicitly
CHR: reinfer-xor-effect @ // { ReinferEffect P{ Xor ?c ?d } ?tau } -- |
{ ReinferEffect ?c ?rho }
{ ReinferEffect ?d ?sig }
{ MakeXor ?rho ?sig ?tau } ;

CHR: reinfer-effect @ // { ReinferEffect P{ Effect ?a ?b ?x ?k } ?tau } -- |
[ ?tau { ?a ?b } vars ?k
  "reinfer" [ make-spool

              P{ MakeEffect ?a ?b f f ?tau }
              P{ CompMode } 3array reverse
            ] new-context
] ;
! [ ?k ]
! [ ?i vars [ Roots boa ] [ Live boa ] bi 2array ]
! { FinishEffect ?tau } ;

! TODO: document this
CHR: force-union @ { PhiMode } { FixpointMode } // { Invalid } -- | ;

! ! * Suspend Reasoning
! ! NOTE: we only do this at the end to make sure we also collect the { FinishEffect } "closing bracket"
! ! Actually, hold on, dual finisheffect markers shouldn't hurt because they are tied to their Makeeffects...
! CHR: suspend-make-effect @ // { MakeEffect ?a ?b ?x ?l ?tau } { CompMode } { ?DeferTypeOf ?q ?sig } -- |
! { SuspendMakeEffect ?a ?b ?x ?l ?tau { ?q ?sig } } ;

! CHR: collect-suspend-pred @ // { SuspendMakeEffect ?a ?b ?x ?l ?tau { ?q ?sig } } AS: ?p <={ body-pred } --
! [ ?l ?p suffix :>> ?k ]
! |
! { SuspendMakeEffect ?a ?b ?x ?k ?tau { ?q ?sig } } ;

! CHR: suspend-do-reinfer @ // { SuspendMakeEffect ?a ?b ?x ?l ?tau { ?q ?sig } } -- |
! { ?TypeOf ?q ?sig }
! { SuspendMakeEffect ?a ?b ?x ?l ?tau ?sig } ;

! GENERIC: maybe-rec-full-type? ( x -- ? )
! M: object maybe-rec-full-type? full-type? ;
! M: Recursive maybe-rec-full-type? effect>> maybe-rec-full-type? ;

! CHR: continue-suspend-make-effect @ // { SuspendMakeEffect ?a ?b ?x ?l ?tau ?sig } -- [ ?sig maybe-rec-full-type? ] |
! { CompMode }
! { MakeEffect ?a ?b f f ?tau }
! [ ?l ] ;

! * Post-Reasoning

! *** Phi Mode
! CHR: discard-non-union-pred @ { PhiMode } <={ MakeEffect } // <={ body-pred } -- | ;
! CHR: discard-leftover-binds @ { PhiMode } <={ MakeEffect } // <={ Bind } -- | ;
! CHR: phi-discard-phi-defs @ { PhiMode } <={ MakeEffect } // <={ Phi } -- | ;

! TODO: this is still tricky... not sure how to test this exhaustively
: pred-live-in-vars? ( pred vars -- ? )
    ! make-effect-vars
    {
        [ [ vars ] dip subset? ]
        [ [ intersects-live-vars ] dip intersects? ]
        [ [ live-vars ] dip subset? ] } 2|| ;

CHR: collect-union-pred @ { PhiMode } { FinishEffect ?tau } // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } { Keep ?p } -- [ ?p ?e make-effect-vars pred-live-in-vars? ]
[ ?p ?l in? not ]
[ ?l ?p suffix :>> ?k ]
|
! FIXME: this should probably also use the mechanism which excludes free vars?
[| | ?p defines-vars ?x union :> y
 { MakeEffect ?a ?b y ?k ?tau } ] ;


CHR: phi-discard-discriminators @ { FinishEffect ?tau } { PhiMode } { MakeEffect __ __ __ __ ?tau } // <={ Discriminator } -- | ;
CHR: phi-discard-leftover-preds @ { FinishEffect ?tau } { PhiMode } { MakeEffect __ __ __ __ ?tau } // <={ body-pred } -- | ;
! TODO: not 100% sure the following isn't working too eagerly...
CHR: phi-discard-keeps @ { FinishEffect ?tau } { PhiMode } { MakeEffect __ __ __ __ ?tau } // <={ Keep } -- | ;

CHR: phi-discard-params @ { FinishEffect ?tau } { PhiMode } { MakeEffect __ __ __ __ ?tau } // <={ Params } -- | ;

! *** Composition Mode
! These are live after the pred has been taken into account

PREFIX-RULES: { P{ CompMode } }

! CHR: collect-call-recursive-input @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallRecursive ?m ?rho ?sig } --
! [ ?rho vars ?e make-effect-vars subset? ]
! [ ?x ?sig vars union :>> ?y ]
! [ ?l ?p suffix :>> ?k ]
! | { MakeEffect ?a ?b ?y ?k ?tau } ;

! CHR: discard-known-iterated-stack @ { FinishEffect ?tau } // { Iterated __ ?s } --
! CHR: discard-known-iterated-stack @ // { Iterated __ ?s } --
! [ ?s sequence? ]
! [ ?s [ [ lastcdr ] same? ] monotonic? ] | ;

! *** Nested Reasoning Triggering
CHR: collect-call-recursive @ { FinishEffect ?tau } // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p P{ CallRecursive ?m ?rho ?sig } --
[ ?rho vars ?sig vars union ?e make-effect-vars intersects? ]
[ ?x ?rho vars union ?sig vars union :>> ?y ]
[ ?l ?p suffix :>> ?k ]
| { MakeEffect ?a ?b ?y ?k ?tau } ;

! *** All other preds
! **** Parameter liveness propagation
CHR: unique-implies-param @ { ImpliesParam ?x ?y } // { ImpliesParam ?x ?y } -- | ;
CHR: remove-non-param-impl @ // { ImpliesParam ?x ?y } -- [ ?y vars empty? ] | ;

CHR: define-implied-param @ { FinishEffect ?tau } // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } { ImpliesParam ?m ?n } --
[ ?m vars ?e make-effect-vars subset? ]
[ ?x ?n union :>> ?y drop t ] |
{ MakeEffect ?a ?b ?y ?l ?tau } ;

CHR: implied-param-join @ // { ImpliesParam ?x ?a } { ImpliesParam ?y ?b } --
[ ?b ?x vars subset? ]
[ ?x vars ?b diff
  ?y vars ?a diff
  union
  :>> ?m ]
[ ?a ?b union :>> ?k ]
| { ImpliesParam ?m ?k } ;

PREFIX-RULES: f
! NOTE: Big change! Use same collection rule for phi finishing as for composition finishing!

! NOTE: this will mess up unification semantics on liveness set var sets, because we unify into existing liveness sets.
! TODO: test that this is well-behaved in phi merging!
! FIXME: This is not valid in the general case.  This is only valid if we are losing track of a local allocation.
! Otherwise, the PushLoc needs to enforce the presence and liveness of any input memory locations!
! At this point, the it is assumed that the allocation is actually not live
! CHR: perform-flushable-loc-op @ { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } // <={ LocOp ?x ?a __ ?b t } -- | [ ?a ?b ==! ] ;
! CHR: perform-flushable-loc-op @ { MakeEffect __ __ __ __ ?tau } // { FinishEffect ?tau } AS: ?p <={ LocOp ?x ?a __ ?b t } -- |
! [ { "losing loc op" ?p } throw ]
! [ "flush beta resolve" print
!   t trace-wakeup set-global f ]
! [ ?a ?b ==! ]
! [ f trace-wakeup set-global f ]
! { FinishEffect ?tau } ;

! CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p vars ?e make-effect-vars intersects? ]
! CHR: collect-body-pred @ // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ body-pred } -- [ ?p live-vars ?e make-effect-vars subset? ]
! NOTE: using overlap right now to extend the set of parameters.  This might be too general to get rid of remaining unused predicates.
! One approach could be to require a certain number of vars to be live, so the rest actually can be derived.  E.g. for a Sum predicate, we will always
! Need two out of three vars to be able to determine the third.  Alternatively, we could reason input/output-style?
! CHR: collect-body-pred @ { FinishEffect ?tau } // AS: ?p <={ body-pred } AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } -- [ ?p ?e pred-live-in-effect? ]
! NOTE: deps should already be present, so we can pluck the predicate
! NOTE: Reverting to the previous intersect/defines vars behavior for now because of instance checks forcing an output type!
! CHR: collect-live-body-pred @ { FinishEffect ?tau } // AS: ?p <={ body-pred } AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } --
CHR: collect-live-body-pred @ { FinishEffect ?tau } // { Collect ?p } AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } --
! [ ?p live-vars ?v subset? ]
! [ ?p ?e make-effect-vars pred-live-in-vars? ]
! [ ?p ?e pred-live-in-effect? ]
[ ?p ?l in? not ]
[ ?l ?p suffix :>> ?k ]
|
[| |
 ! FIXME: defines-vars behavior.  Is that adding root scope? or just new rels?
 ! ?p defines-vars ?x union :> y
 ?p vars ?p free-effect-vars diff ?x union :> y
 { MakeEffect ?a ?b y ?k ?tau } ] ;

! ! FIXME: Don't use this kind of special case!
! CHR: collect-boa @ { FinishEffect ?tau } // AS: ?e P{ MakeEffect ?a ?b ?x ?l ?tau } AS: ?p <={ Boa ?c ?i ?o } --
! ! [ ?i ?o [ vars ?e make-effect-vars in? ] bi@ or ]
! [ ?p vars ?e make-effect-vars intersects? ]
! [ ?l ?p suffix :>> ?k ]
! [ ?x ?p vars union :>> ?y ] |
! { MakeEffect ?a ?b ?y ?k ?tau } ;


CHR: losing-undefined-loc-spec @ { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } { Def ?l } // AS: ?p <={ LocSpec ?x . __ } --
[ ?x ?l in? not ] | [ { "locspec has no definition" ?p } throw ] ;

CHR: discard-implied-param @ { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } // <={ ImpliesParam } -- | ;
CHR: incomplete-scope @ { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } // { Scope ?l ?r } -- | [ { ?l ?r "losing scope" } throw ] ;
CHR: discard-liveness-preds @ { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } // <={ liveness-pred } -- | ;

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
PREFIX-RULES: f
! *** Discard unrelated predicates

CHR: apply-effect-not-known @ { FinishEffect __  } // { ApplyEffect M{ ?rho } ?i ?o } -- | [ "applying unknown effect" throw ] ;
CHR: losing-call-effect @ { FinishEffect ?tau } <={ MakeEffect } // AS: ?p P{ CallEffect __ __ __ } -- | [ { ?p "discarding a call-effect predicate" } throw ] ;
CHR: losing-macro-call @ { FinishEffect ?tau } <={ MakeEffect } // AS: ?p <={ MacroCall } -- | [ { ?p "discarding a macro call predicate" } throw ] ;
CHR: losing-unresolved-iteration @ { FinishEffect ?tau } <={ MakeEffect } // AS: ?p <={ Iterated } -- | [ { ?p "discarding unresolved iteration predicate" } throw ] ;
CHR: losing-unresolved-loc-op @ { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } // AS: ?p <={ LocOp } --
[ ?p PushLoc? ?p local?>> and not ]
| [ { ?p "discarding unresolved location effect" } throw ] ;
! Still pretty fragile....
CHR: perform-dead-push-loc @ { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } // { PushLoc M{ ?x } ?a __ ?b ?t } -- |
[ ?a ?b ==! ] ;
CHR: cleanup-incomplete @ { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } // AS: ?p <={ body-pred } -- | ;

! This is triggered if phi mode is aborted
CHR: finish-disjoint-effect @ { PhiMode } { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } // { Invalid } -- |
[ ?tau null ==! ] ;

! This is triggered if composition modes determines the effect will terminate
CHR: finish-invalid-effect @ { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } // { Invalid } -- |
[ ?tau P{ Effect ?a ?b f { P{ Invalid } } } ==! ] ;


! NOTE: changing this to immediately re-infer any xors!
CHR: finish-rebuild-xor-call-effect @ { MakeEffect ?a ?b ?x ?l M{ ?tau } } // { FinishEffect ?tau } -- [ ?l [ CallXorEffect? ] any? ] |
[| | ?l split-xor-call-preds :> ( then-preds else-preds )
 P{ Effect ?a ?b ?x then-preds } fresh-effect :> then-effect
 P{ Effect ?a ?b ?x else-preds } fresh-effect :> else-effect
 P{ ReinferEffect then-effect ?rho }
 P{ ReinferEffect else-effect ?sig }
 2array
]
{ MakeXor ?rho ?sig ?z }
{ CheckXor f ?z ?tau }
{ FinishEffect ?tau } ;


CHR: finish-valid-effect @ { FinishEffect ?tau } AS: ?e P{ MakeEffect ?a ?b ?x ?l M{ ?tau } } // --
[ ?x ?a vars diff ?b vars diff
  ! FIXME: this exposes what seems to be a bug in the term solver, probably something going wrong when f is assigned to a binding,
  ! resulting in a recursive-term-error in case for checking strange stuff...
  dup empty? [ drop f ] when
  :>> ?y drop t ]
|
[ ?tau P{ Effect ?a ?b ?y ?l }
  ! dup check-for-lost-location-effects
  ==! ] ;

! NOTE: re-inserting the FinishEffect Predicates because they don't get reactivated by substitution
CHR: finish-phi-reasoning @ // { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } { PhiMode } -- [ ?tau term-var? not ] | { FinishEffect ?tau }
! [ [ P{ PhiDone } ] no-context ]
{ PhiDone } ;

CHR: finish-compositional-reasoning @ // { FinishEffect ?tau } { MakeEffect __ __ __ __ ?tau } { CompMode } -- [ ?tau term-var? not ] | { FinishEffect ?tau } ;

! * Token removal
CHR: finish-effect-done @ // { FinishEffect ?tau } -- [ ?tau term-var? not ] | ;

;
