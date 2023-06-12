USING: accessors arrays chr.factor chr.factor.util chr.parser classes
classes.tuple combinators.short-circuit kernel lists sequences sets terms ;

IN: chr.factor.intra-effect.liveness

! * Calculating what to include in inference

! The idea is to only collect predicates if they add relevant predicative information
! to the resulting effect.  We want to include variables which are necessary to be able
! to identify those constraints.
! Approach:
! - they must be related to input or output values.  Any variables which are
!   intermediates in that "chain" are added to a local live set.
! - constraints which only add information "circularly" between variables should
!   be excluded

! The common case to solve is to drop predicates on values which are lost during
! composition, but keep the reasoning between new input/output input/input, maybe
! output/output values

CHRAT: chr-factor-liveness {  }

! Flattening

! ** Scoping

: make-imply ( left right -- pred )
    [ vars ] bi@ 2dup [ empty? not ] both? [ Imply boa ] [ 2drop f ] if ;

PREFIX-RULES: { P{ Liveness } }
! ** Live set hous-keeping
UNION: merging-set Def Use Live ;

! NOTE: this is not optimized right now
! CHR: subsume-liveness-set @ AS: ?a <={ merging-set ?x } // AS: ?b <={ merging-set ?y } --
! [ ?a ?b [ class-of ] same? ] [ ?y ?x subset? ] | ;
! CHR: merge-liveness-set @ // AS: ?a <={ merging-set ?x } AS: ?b <={ merging-set ?y } --
! [ ?a ?b [ class-of ] same? ] | [ ?x ?y union 1array ?a class-of slots>tuple ] ;


! NOTE: this is for catching the case where we perform additional stack unification during live set
! reasoning
CHR: malformed-liveness-set @ // AS: ?a <={ merging-set ?x } -- [ ?x [ term-var? ] all? not ] |
[ { ?a "malformed-liveness-set" } throw ] ;

: valid-live-set? ( x -- ? ) [ term-var? ] all? ;

! TODO: check whether removing the subsumption rule is actually faster overall?
! CHR: normalize-def-set @ // { Def ?x } -- [ ?x valid-live-set? not ] [ ?x vars :>> ?y ] | { Def ?y } ;
CHR: subsume-def-set @ { Def ?x } // { Def ?y } -- [ ?y ?x subset? ] | ;
CHR: merge-def-set @ // { Def ?x } { Def ?y } -- [ ?x ?y union :>> ?z ]
| { Def ?z } ;

! CHR: normalize-live-set @ // { Live ?x } -- [ ?x valid-live-set? not ] [ ?x vars :>> ?y ] | { Live ?y } ;
CHR: subsume-live-set @ { Live ?x } // { Live ?y } -- [ ?y ?x subset? ] | ;
CHR: merge-live-set @ // { Live ?x } { Live ?y } -- [ ?x ?y union :>> ?z ]
| { Live ?z } ;

! CHR: normalize-use-set @ // { Use ?x } -- [ ?x valid-live-set? not ] [ ?x vars :>> ?y ] | { Use ?y } ;
CHR: subsume-use-set @ { Use ?x } // { Use ?y } -- [ ?y ?x subset? ] | ;
CHR: merge-use-set @ // { Use ?x } { Use ?y } -- [ ?x ?y union :>> ?z ]
| { Use ?z } ;

CHR: new-sub-scope @ // { SubScope ?i ?o } --
! [ ?i value-vars :>> ?l ] [ ?o value-vars :>> ?r ]
[ ?i vars :>> ?l ] [ ?o vars :>> ?r ]
[ ?l ?r union :>> ?v ] | { Live ?v } { Use ?l } { Def ?r } ;

CHR: new-scope @ // { Scope ?i ?o } --
! [ ?i value-vars :>> ?l ] [ ?o value-vars :>> ?r ]
[ ?i vars :>> ?l ] [ ?o vars :>> ?r ]
[ ?l ?r union :>> ?v ] | { Live ?v } { Def ?l } { Use ?r } ;

! ** Dependency Generation
! *** Unconditional
UNION: call-pred CallRecursive CallEffect CallXorEffect PrimCall GenericDispatch ;
GENERIC: pred-def-use ( pred -- defs uses )
M: body-pred pred-def-use drop f f ;
M: call-pred pred-def-use [ out>> ] [ in>> ] bi [ value-vars ] bi@ ;
M: CallEffect pred-def-use
    [ call-next-method ] keep thing>> suffix ;
M: LocalAllocation pred-def-use obj>> 1array f ;
M: Eq pred-def-use dup val2>> term-var? not
    [ val>> 1array ] [ drop f ] if f ;

! CHR: body-pred-def-use-live @ AS: ?p <={ body-pred } // { Live ?l } -- [ ?p pred-def-use :>> { ?a ?b } [ empty? ] both? not ] [ ?a ?b [ ?l subset? ] both? not ] |
! [ ?a ?b append ?l union Live boa ] ;

CHR: body-pred-defs @ AS: ?p <={ body-pred } // { Def ?l } -- [ ?p pred-def-use drop :>> ?x ?l subset? not ] |
[ ?l ?x union Def boa ] ;

CHR: body-pred-uses @ AS: ?p <={ body-pred } // { Use ?l } -- [ ?p pred-def-use nip :>> ?x ?l subset? not ] |
[ ?l ?x union Use boa ] ;

CHR: call-pred-io-is-live @ AS: ?p <={ call-pred } // { Live ?l } -- [ ?p pred-def-use :>> { ?a ?b } [ ?l subset? ] both? not ] |
[ ?a ?b append ?l union Live boa ] ;

! *** Conditional

GENERIC: imply-def ( def pred -- modes )
M: body-pred imply-def 2drop f ;
M: commutative-op imply-def ( def pred -- modes )
    vars set-cut dup length 1 =
    [ make-imply ] [ 2drop f ] if ;

! NOTE: allowing empty antecedent here!
: maybe-make-imply ( def left right -- mode/f )
    [ vars ] bi@
    { [ 2nip empty? not ]
      [ drop swap subset? ]
      [ nip swap subset? not ]
      [ nipd Imply boa ] } 3&& ;

M: Slot imply-def ( def pred -- modes )
    [ val>> ] [ n>> 2array ] [ val>> ] tri
    maybe-make-imply ;
! If the slot and the object is defined, the location is defined
M: SlotLoc imply-def
    [ obj>> ] [ n-val>> 2array ] [ loc>> ] tri
    maybe-make-imply ;

! ! If the location is defined, the item is defined.
! ! NOTE: Probably have to change this to unconditional use of the item?
! ! See below rules where this is changed to be a scoping action based on location liveness
! M: LocPop imply-def
!     [ loc>> ] [ item>> ] bi maybe-make-imply ;
M: MacroCall imply-def
    [ args>> ] [ out-quot-val>> ] bi maybe-make-imply ;
M: Eq imply-def
    [ val>> ] [ val2>> ] bi
    [ maybe-make-imply ]
    [ swap maybe-make-imply ] 3bi xor ;

CHR: def-used-is-live @ { Def ?l } { Use ?r } // { Live ?v } --
[ ?l ?r intersect :>> ?a empty? not ] [ ?a ?v diff :>> ?b empty? not ]
[ ?v ?b union :>> ?c ] | { Live ?c } ;

! NOTE: this transports the lhs of the implication into the use set
CHR: have-implied-def-use @ { Def ?l } // { Imply ?x ?y } { Use ?r } --
[ ?y ?r subset? ] [ ?x ?r intersects? not ] [ ?x ?l subset? ]
[ ?r ?x union :>> ?s ] |
! { Live ?x }
{ Use ?s } ;

CHR: redundant-implication @ { Use ?r } // { Imply ?x ?y } -- [ ?x ?r subset? ] [ ?y ?r subset? ] | ;

! TODO: check if this can be done with guard vars too
CHR: body-pred-imply-def @ AS: ?p <={ body-pred } // { Def ?l } -- [ ?l ?p imply-def ] |
[ ?l ?p imply-def [ out>> ?l union Def boa ] keep 2array ] ;

! If a value is used, all it's defining characteristics are also used
CHR: used-val-pred-used-by-value @ AS: ?p <={ val-pred ?x . ?a } // { Use ?r } -- [ ?x ?r in? ] [ ?a vars :>> ?b ?r subset? not ] |
[ ?b ?r union Use boa ] ;

! ! This makes sure to keep all "attached" predicates to a value
! CHR: live-val-pred-is-live @ { Live ?v } <={ val-pred ?x . ?r } // -- [ ?x ?v in? ] [ ?r vars ?v diff :>> ?y empty? not ] |
! { Live ?y } ;
! TODO: might need better generalization! either to expr preds, or to all?
! NOTE: this reasoning might need to be transitive! In that case, might actually need more cones?
! No! having the rel-preds being too contagious was actually a problem for loop var stuff!
! CHR: live-val-uses-rel-preds @ <={ rel-pred M{ ?x } M{ ?y } . __ } // { Live ?v } --
CHR: notsame-live-modes @ { NotSame ?x ?y } // { Live ?v } --
[ ?x ?v in?  ?y ?v in? not and :>> ?a
  ?y ?v in?  ?x ?v in? not and xor ] |
[ ?v ?a ?y ?x ? suffix Live boa ] ;


! TODO: Extend this to slot-locs, since they are not val-preds
CHR: used-object-uses-slot-loc @ { SlotLoc ?x ?o __ } // { Use ?r } -- [ ?o ?r in? ] [ ?x ?r in? not ] |
[ ?r ?x suffix Use boa ] ;

! set-slot must be live:
! object is defined but not used
! location is defined
! LocPop is not local
! PushLoc is not local
! Reasoning:
!  - a non-local push-loc must always be live. -> a non-local push-loc always uses the location and the item
!  - a non-local loc-pop must always be live. (volatility assumption) -> the location is always used and the item defined
! thus: - a non-local loc-op always uses the location -> since the location must be defined, the loc-op must be live
! - any live loc-pop always has the item defined
! - any live push-loc always has the item used

! CHR: non-local-loc-op-uses-loc @ <={ LocOp ?x __ ?s __ f . __ } // { Use ?l } -- [ ?s vars ?l subset? ?x ?l in? and not ] |
! [ ?s vars ?x suffix ?l union Use boa ] ;

! [ (clone) 2 slot ] loc-pop must be live:
! - local loc-pop
! thus: any loc-pop must always be live. -> all loc-ops except for local loc-pushes unconditionally use the location
CHR: loc-op-must-use-loc @ AS: ?p <={ LocOp M{ ?x } __ ?s __ ?m . __ } // { Use ?l } -- [ ?s vars ?l subset? ?x ?l in? and not ]
[ ?m not ?p LocPop? or ] | [ ?s vars ?x suffix ?l union Use boa ] ;

CHR: live-loc-pop-defs @ { LocPop ?x __ ?s __ __ __ } { Use ?r } // { Def ?l } -- [ ?x vars ?r subset? ] [ ?s vars :>> ?b ?l subset? not ] |
[ ?l ?b union Def boa ] ;

CHR: live-push-loc-uses @ { PushLoc ?x __ ?s __ __ } // { Use ?r } -- [ ?x vars ?r subset? ] [ ?s vars :>> ?b ?r subset? not ] |
[ ?r ?b union Use boa ] ;


! ** Collection

PREFIX-RULES: { P{ Collection } }
! "Liveness Anchor"
GENERIC: upper-scope-vars ( pred -- term )
M: body-pred upper-scope-vars ;
M: Instance upper-scope-vars val>> ;
M: DeclareStack upper-scope-vars classes>> ;
M: LocalAllocation upper-scope-vars obj>> ;
! M: LocOp upper-scope-vars [ loc>> ] [ item>> ] bi 2array ;
! Note: not including the item here because that is part of conditional scoping on the location
M: LocOp upper-scope-vars loc>> ;
M: CallEffect upper-scope-vars thing>> ;
M: CallRecursive upper-scope-vars drop { } ;
M: CallXorEffect upper-scope-vars drop { } ;
M: PrimCall upper-scope-vars [ in>> ] [ out>> ] bi [ value-vars ] bi@ 2array ;

CHR: collect-covered-body-pred @ { Live ?a } // AS: ?p <={ body-pred } --
[ ?p upper-scope-vars [ vars :>> ?v drop ] keep ] ! [ ?v empty? not ]
[ ?v ?a subset? ] |
{ Collect ?p } ;

! ** Predicate-independent handling

! ! ** Collection of Other Preds
! PREFIX-RULES: { P{ CompMode } }

! ! *** Local allocation
! CHR: local-allocation-is-defined @ { Live __ } { LocalAllocation __ ?o } // -- | { Def { ?o } } ;

! ! NOTE: putting this here only so it will not be collected too early.  Not good from a sequencing perspective.
! ! Should probably rework this to first completely generating the def/use tree, and then collecting, and then seeing
! ! where optimizations can safely be performed.
! CHR: slot-modes @ { Slot ?o ?n ?v } // { Def ?l } --
! [ { ?o ?n } vars ?l subset? ] [ ?v ?l in? not ] [ ?l ?v suffix :>> ?m ]
! | { Def ?m } [ { ?o ?n } ?v make-imply ] ;



! ! ** CallEffect and friends

! ! NOTE: Treat the scope as if the quotation is part of the bracket?
! CHR: collect-call-effect-define-scope @ { Live __ } // AS: ?p P{ CallEffect ?q ?a ?b } --
! [ ?q ?a cons :>> ?l ] |
! { Collect ?p } { SubScope ?l ?b } ;


! ! NOTE: if the stack vars are the same, then we only define a relationship between the vars on top of the stack?
! CHR: collect-inline-call-define-scope @ { Live __  } // AS: ?p <={ inline-call-pred __ ?a ?b } -- |
! { Collect ?p }
! { SubScope ?a ?b } ;

! CHR: collect-unresolved-prim-call-define-scope @ { Live __ } // AS: ?p P{ PrimCall ?w ?a ?b } -- |
! { Collect ?p } { SubScope ?a ?b } ;


! ! push-loc: stack transfer from lambda realm to loc stack.  Is used at the point of the push
! CHR: collect-push-loc @ { Live ?v } // AS: ?p P{ PushLoc ?l ?a ?s ?b ?m } --
! [ ?l vars ?v subset? ]
! [ ?s vars ! ?a vars ?b vars append append
!   :>> ?x ] | { Collect ?p } { Use ?x }
! { Live ?x } ;

! ! loc-pop: stack transfer from loc-stack to lambda-realm.  Is defined at the point of the pop
! CHR: collect-loc-pop @ { Live ?v } // AS: ?p P{ LocPop ?l ?a ?s ?b ?m __ } --
! [ ?l vars ?v subset? ]
! [ ?s vars ! ?a vars ?b vars append append
!   :>> ?x ] | { Collect ?p } { Def ?x }
! { Live ?x } ;

! CHR: collect-iterated @ { Live __ } // AS: ?p <={ Iterated __ { ?i ?b ?c ?d ?o } } -- |
! { Collect ?p }
! { SubScope ?i ?d }
! { SubScope ?d ?o }
! { Scope ?b ?c } ;

! CHR: collect-boa-is-a-scope @ { Live __ } // AS: ?p P{ Boa ?c ?i ?o } -- [ ?c ?i cons :>> ?a ] |
! { Collect ?p }
! { SubScope ?a ?o } ;

! ! NOTE: this is always a same-last-cdr scope.  Shouldn't matter though?
! ! Actually, this is effectful.  It is only admissible to prune something like this if it is flushable.
! ! TODO: add rule for flushables, or handle flushable in a general way!
! ! CHR: collect-generic-dispatch-is-scope @ { Live ?l } { Def ?a } { Use ?b } // AS: ?p P{ GenericDispatch ?w ?d ?v ?i ?o } --
! ! [ ?v ?l subset? ] [ ?v ?b subset? ] [ ?d ?l subset? ] [ ?d ?a subset? ] | { Collect ?p } { SubScope ?i ?o } ;
! CHR: collect-generic-dispatch-is-scope @ { Live __ } // AS: ?p P{ GenericDispatch ?w ?d ?v ?i ?o } --
! | { Collect ?p } { SubScope ?i ?o } ;


! ! This is analogous to the live-val-pred-is-live assumption: If we have a live object, all defined aspects of it
! ! must be live too.  Thus, if an object is live, it's slots are live too. ( provided the location is defined? )
! ! NOTE: actually, the slotloc predicate can become abandoned if there are no locops defined on it!
! ! CHR: live-slot-loc-is-live @ { SlotLoc ?x ?o ?n } { Live ?v } // -- [ ?x ?v in? not ] [ ?o ?v in? ]
! ! | { Live { ?x ?n } } ;
! ! CHR: live-location-is-live @ <={ LocSpec ?x . ?r } // { Live ?l } -- [ ?x ?l in? ] [ ?r vars :>> ?s ?l subset? not ]
! ! [ ?l ?s union :>> ?m ] | { Live ?m } ;

! PREFIX-RULES: { P{ CompMode } P{ Live __ } }

! ! ! This is used so as to not always have to touch Def manually
! ! CHR: imply-extends-def @ { Imply ?x ?y } // { Def ?l } --
! ! [ ?x ?l subset? ] [ ?y ?l subset? not ] [ ?y ?l union :>> ?m ] |
! ! { Def ?m } ;

! CHR: literal-is-defined @ { Eq ?x A{ ?v } } // -- | { Def { ?x } } ;
! ! ** Predicate-speficic Modes and Collection
! ! *** Locations

! ! SlotLoc operations are generally considered to be effectful.  It is an error if there is a sequential operation on
! ! an undefined location.  Only for local allocations unused locations can be ignored.  For those, the effect operations
! ! are nop'd before effect body predicate collection.

! CHR: local-loc-push-modes @ { PushLoc M{ ?x } __ __ __ t } { SlotLoc ?x ?o __ } { Def ?l } { Use ?r } // --
! [ ?x ?l in? ] [ ?o ?r in? ] [ ?x ?r in? not ] | { Use { ?x } } ;

! CHR: unknown-alloc-loc-push-use-loc @ { PushLoc M{ ?x } __ __ __ f } { SlotLoc ?x ?o __ } // -- | { Use { ?x } } ;

! CHR: loc-pop-modes @ { LocPop M{ ?x } __ ?s __ __ __ } // { Use ?r } -- [ ?x ?r in? not ] [ ?s vars ?r intersect :>> ?y empty? not ]
! [ ?r ?x suffix :>> ?m ] | [ ?x ?y make-imply ] { Use ?m }  ;

! CHR: defined-location-is-defined @ <={ LocSpec ?x . ?r } // { Def ?l } -- [ ?x ?l in? not ] [ ?r vars ?l subset? ]
! [ ?l ?x suffix :>> ?m ] | { Def ?m } ;

! ! TODO: this may need to be extended to implications? Right now adjusting the modes for PushLoc
! ! Yes, need implication or we are losing the
! CHR: used-slot-loc-slot-is-used @ { SlotLoc ?x ?o ?n } // { Use ?r } -- [ ?x ?r in? ] [ { ?o ?n } vars ?r subset? not ]

! [ ?r { ?o ?n } vars union :>> ?m ] | { Use ?m } ;

! ! *** Relations
! ! TODO: only add these if it makes sense for optimization?
! ! CHR: rel-pred-modes @ <={ rel-pred M{ ?x } M{ ?y } } // -- | [ ?x ?y make-imply ] [ ?y ?x make-imply ] ;

! CHR: eq-def-mode-1 @ { Eq M{ ?x } M{ ?y } } // { Def ?l } -- [ ?x ?l in? ]
! [ ?y ?l in? not ] [ ?l ?y suffix :>> ?m ] | { Def ?m } [ ?x ?y make-imply ] ;
! CHR: eq-def-mode-2 @ { Eq M{ ?y } M{ ?x } } // { Def ?l } -- [ ?x ?l in? ]
! [ ?y ?l in? not ] [ ?l ?y suffix :>> ?m ] | { Def ?m } [ ?x ?y make-imply ] ;

! ! *** Mathematical Operations

! ! TODO: one of these is possibly never used?
! ! Nope, seems like we need all of them, or another error with scoping exists?
! ! CHR: commutative-op-modes @ <={ commutative-op ?z ?x ?y } // -- |
! CHR: commutative-op-extend-def @ AS: ?p <={ commutative-op } // { Def ?l } --
! [ ?l ?p vars set-cut :>> { ?x ?y } nip length 1 = ]
! [ ?l ?y first suffix :>> ?m ] | { Def ?m } [ ?x ?y make-imply ] ;

! ! CHR: commutative-op-extend-use @ AS: ?p <={ commutative-op } { Def ?l } // { Use ?r } --
! ! [ ?l ?p vars set-cut :>> { ?x ?y } drop length 2 = ]
! ! [ ?l ?y first suffix :>> ?m ] | { Def ?m } ;

! ! *** Other expr preds
! ! Value Predicates are contagious

! PREFIX-RULES: { P{ CompMode } }

! PREFIX-RULES: { P{ CompMode } P{ Live __ } }

! ! NOTE: seems to be too contagious!
! ! CHR: used-val-pred-uses-value @ { Use ?r } AS: ?p <={ val-pred ?x . ?a } // -- [ ?x ?r in? not ] [ ?a vars ?r intersects? ] |
! ! { Use { ?x } } ;

! ! *** Macro-likes
! CHR: macro-call-modes @ { MacroCall __ ?a ?q } // -- | [ ?a ?q make-imply ] ;

;
