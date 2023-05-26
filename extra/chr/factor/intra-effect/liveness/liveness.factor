USING: accessors arrays chr.factor chr.factor.util chr.parser classes
classes.tuple kernel lists sequences sets terms ;

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
    ! [ vars ] bi@ 2dup [ empty? not ] both? [ f swap Path boa ] [ 2drop f ] if ;

UNION: bracket Right Left ;
CHR: duplicate-bracket @ AS: ?a <={ bracket ?s __ } // AS: ?b <={ bracket ?s __ } -- [ ?a ?b [ class-of ] same? ] | [ { ?a ?b "duplicate bracket" } throw ] ;

! CHR: scope-defines-live @ <={ Scope ?l ?r } // --
! [ ?l value-vars ?r value-vars union :>> ?v ] | { Live ?v } ;

! CHR: scope-brackets @ // { Scope ?l ?r } --
! [ ?l stack-vars :>> ?a drop :>> ?x ]
! [ ?r stack-vars :>> ?b drop :>> ?y ] | { Left ?a ?x } { Right ?b ?y } ;

! CHR: subscope-is-closed @ // { SubScope ?l ?r } -- [ ?l lastcdr ?r lastcdr == ]
! [ ?l value-vars :>> ?a ] [ ?r value-vars :>> ?b ]
! | [ ?a ?b make-imply ] ;

! CHR: subscope-brackets @ // { SubScope ?l ?r } --
! [ ?l stack-vars :>> ?a drop :>> ?x ]
! [ ?r stack-vars :>> ?b drop :>> ?y ] | { Right ?a ?x } { Left ?b ?y } ;

! CHR: inner-scope-is-closed @ // { Scope ?l ?r } -- [ ?l lastcdr ?r lastcdr :>> ?s == ]
! [ ?l value-vars :>> ?a ] [ ?r value-vars :>> ?b ] |
! { Left ?s ?a } { Right ?s ?b } ;

! NOTE: Gotta be careful here.  The left scope is the one already present in the store, thus it
! must always be the outer scope, which is actually a right bracket!
! CHR: left-subscope @ { Scope ?a ?b } { Scope ?x ?y } // -- [ ?a lastcdr ?x lastcdr :>> ?s == ]
! [ ?a value-vars :>> ?r ] [ ?x value-vars :>> ?l ]
! | { Left ?s ?l } { Right ?s ?r } ;

! CHR: right-subscope @ { Scope ?a ?b } { Scope ?x ?y } // -- [ ?b lastcdr ?y lastcdr :>> ?s == ]
! [ ?b value-vars :>> ?l ] [ ?y value-vars :>> ?r ]
! | { Left ?s ?l } { Right ?s ?r } ;

! CHR: scope-is-closed @ { Left ?l __ } { Right ?r __ } // { Scope ?a ?b } -- [ ?l ?a lastcdr == ] [ ?r ?b lastcdr == ] | ;

PREFIX-RULES: { P{ CompMode } }
! "Liveness Anchor"
GENERIC: upper-scope-vars ( pred -- term )
M: body-pred upper-scope-vars drop f ;
M: expr-pred upper-scope-vars ;
M: val-pred upper-scope-vars ;
M: Instance upper-scope-vars val>> ;
M: LoopVar upper-scope-vars ;
! M: Iterated upper-scope-vars stuff>> [ first ] [ last ] bi 2array ;
! M: CallEffect upper-scope-vars thing>> ;
! M: CallEffect upper-scope-vars drop f ;
! M: CallRecursive upper-scope-vars drop f ;
! ! M: CallXorEffect upper-scope-vars [ in>> ] [ out>> ] bi 2array ;
! M: CallXorEffect upper-scope-vars drop f ;
M: MacroCall upper-scope-vars ;
M: Counter upper-scope-vars ;
M: Declare upper-scope-vars ;
M: DeclareStack upper-scope-vars classes>> ;


! UNION: merging-set Given Define ;
UNION: merging-set Def Use Live ;

! NOTE: this is not optimized right now
! CHR: subsume-liveness-set @ AS: ?a <={ merging-set ?x } // AS: ?b <={ merging-set ?y } --
! [ ?a ?b [ class-of ] same? ] [ ?y ?x subset? ] | ;
! CHR: merge-liveness-set @ // AS: ?a <={ merging-set ?x } AS: ?b <={ merging-set ?y } --
! [ ?a ?b [ class-of ] same? ] | [ ?x ?y union 1array ?a class-of slots>tuple ] ;

! TODO: check whether removing the subsumption rule is actually faster overall?
CHR: subsume-def-set @ { Def ?x } // { Def ?y } -- [ ?y ?x subset? ] | ;
CHR: merge-def-set @ // { Def ?x } { Def ?y } -- [ ?x ?y union :>> ?z ]
| { Def ?z } ;

CHR: subsume-live-set @ { Live ?x } // { Live ?y } -- [ ?y ?x subset? ] | ;
CHR: merge-live-set @ // { Live ?x } { Live ?y } -- [ ?x ?y union :>> ?z ]
| { Live ?z } ;

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
! CHR: have-live @ { Given ?x } { Define ?y } // { Live ?v } -- [ ?x ?y intersect :>> ?z empty? not ]
! [ ?z ?v subset? not ]
! [ ?z ?v union :>> ?a ] [ ?y ?z ]
! |
! CHR: already-live @ { Live ?x } // { Live ?y } -- [ ?y ?x subset? ] | ;
! CHR: merge-live @ // { Live ?x } { Live ?y } -- [ ?x ?y union :>> ?z ] | { Live ?z } ;

! ** Predicate-independent handling
! CHR: param-is-live @ { Left ?a } { Right ?b } // { Live ?c } -- [ ?a ?b intersect :>> ?x ?c subset? not ]
! [ ?c ?x union :>> ?d ] | { Live ?d } ;

! misnomer...
! usually used as ( existing possible-extension -- things-connecting-it new-things )
: set-cut ( set1 set2 -- common in-set-2-but-not-set-1 )
    members [ swap in? ] with partition ;

CHR: circular-path @ // { Path ?a ?m ?b } -- [ ?a ?b intersects? ] | [ { ?a ?m ?b "circular path" } throw ] ;
CHR: defunct-path @ // { Path ?a ?m ?b } -- [ ?a ?m intersects? ?b ?m intersects? or ] | [ { ?a ?m ?b "malformed path" } throw ] ;

CHR: defunct-imply @ // { Imply ?x ?y } -- [ ?x ?y intersects? ] | [ { ?x ?y "defunct imply" } throw ] ;
CHR: duplicate-imply @ { Imply ?x ?y } // { Imply ?x ?y } -- | ;

! CHR: duplicate-imply @ { Path ?x ?v ?y } // { Path ?x ?v ?y } -- | ;
CHR: subsume-path @ { Path ?a ?m ?b } // { Path ?c ?n ?d } -- [ ?a ?c set= ] [ ?n ?m subset? ] [ ?b ?d set= ] | ;

! NOTE: losing those if the path is not scoped!
! FIXME: might have to use contexts with the scopes if they are well-behaved?
! CHR: impossible-path-left @ { Left ?x } // { Path __ __ ?b } -- [ ?b ?x intersects? ] | ;
! CHR: impossible-path-right @ { Right ?x } // { Path ?a __ __ } -- [ ?a ?x intersects? ] | ;
CHR: impossible-path @ { Left ?s ?x } { Right ?s ?y } // { Path ?a __ ?b } -- [ ?a ?y intersects? ] [ ?b ?x intersects? ] | ;

CHR: have-complete-path @ { Left ?s ?x } { Right ?s ?y } { Path ?a ?m ?b } // --
[ ?a ?x subset? ] [ ?b ?y subset? ] | { Live ?m } ;

! { Path { a b } { x } { c d } } { Path { c d x } { y } { e f } } --> { Path { a b } { c d x y } { e f } }

! NOTE: joining with allowing inner vars does seem to violate order independence condition,
! since paths can continue to be built even though they would be done if the brackets were in
! the store already.  Some possible fixes:
! 1. Don't allow overlap with the path-internal vars after all
! 2. Don't allow already known live vars in the path-internal vars
! 3. Don't allow vars which are in a left or right set already in the path-internal vars
! For now, trying 2.

! ! Angst...
! ! CHR: join-path-right @ { Live ?v } // { Path ?a ?x ?b } { Path ?c ?y ?d } --
! ! That version below still works with the messed up sum example, but not with slots
! ! XXX Fixing that issue via turning the Slot predicate into an expr-pred, so that
! ! the full complexity of the slot connections is not needed for literal slot contents
! ! CHR: join-path-right @ <={ Left } <={ Right } { Live ?v } { Path ?a ?x ?b } // { Path ?c ?y ?d } --
! ! CHR: join-path-right @ { Live ?v } { Path ?c ?y ?d } // { Path ?a ?x ?b } --
! CHR: join-path-right @ { Live ?v } { Path ?a ?x ?b } { Path ?c ?y ?d } // --
! [ ?a ?d intersects? not ]
! [ ?a ?y intersects? not ]
! [ ?b ?x union :>> ?l
!   ?c swap subset? ] [ ?d ?l intersects? not ] [ ?l ?c union ?v diff :>> ?m ]
! | { Path ?a ?m ?d } ;

! ! CHR: join-path-left @ { Live ?v } // { Path ?a ?x ?b } { Path ?c ?y ?d } --
! ! CHR: join-path-left @ <={ Left } <={ Right } { Live ?v } { Path ?c ?y ?d } // { Path ?a ?x ?b } --
! CHR: join-path-left @ { Live ?v } { Path ?a ?x ?b } { Path ?c ?y ?d } // --
! [ ?a ?d intersects? not ]
! [ ?x ?d intersects? not ]
! [ ?c ?y union :>> ?l
!   ?b swap subset? ] [ ?a ?l intersects? not ] [ ?l ?b union ?v diff :>> ?m ]
! | { Path ?a ?m ?d } ;

! ** Collection of Other Preds
PREFIX-RULES: { P{ CompMode } }

! ! This does not feel hacky at all, nope....
! CHR: mask-scope-vars @ { Left ?rho ?a } { Right ?rho ?b } { Mask ?rho ?v } // { Live ?x } --
! [ ?v ?x intersects? ] [ ?v ?a diff ?b diff :>> ?c empty? not ] [ ?x ?c diff :>> ?y ] |
! { Live ?y } ;


! CHR: body-pred-is-covered @ { Left ?a } { Right ?b } // AS: ?p <={ body-pred } --
! CHR: body-pred-is-covered @ { Live ?a } // AS: ?p <={ body-pred } --
CHR: body-pred-is-covered @ { Live ?a } // AS: ?p <={ body-pred } --
! CHR: body-pred-is-covered @ { Given ?x } { Define ?y } // AS: ?p <={ body-pred } --
! [ ?p upper-scope-vars vars :>> ?v ] [ ?v ?a subset? ] ! [ ?v ?b subset? ]
[ ?p upper-scope-vars [ vars :>> ?v drop ] keep ] [ ?v ?a subset? ] ! [ ?v ?b subset? ]
! [ ?p vars :>> ?v ] [ ?v ?a subset? ] ! [ ?v ?b subset? ]
| { Collect ?p } ;



! ** CallEffect and friends

! Here's a revolutionary claim: There cannot be any non-live CallEffect and CallRecursive predicates:
! Explanation:
! 1. If there is a CallEffect predicate, the whole type is only valid iff there is something valid to
!    be called.
! 2. If something callable is not called, it will not be activated in a
!    CallEffect.  It can still be dropped
! 3. If the results of a CallEffect are not needed, that would only possibly apply
!    to any separate objects on the output stack.  The output stack itself is
!    always needed as it is part of the control flow, which is always live
!    according to the previous assumptions.

! NOTE: Unfortunately, found one exception, and this is the one where we insert an inline loop
! callrecursive on the iteration breaking.
! NOTE NOTE: Actually, that one is an error I think.  It happens when we lose an Iterated construct
! and thus don't activate the break-recursive rule.

! Nonetheless, it seems like in general the quotation vars of CallEffect preds are always in the live set.

! Thus, Lemma: All scopes in which predicates can be valid are defined by either
! the parent "MakeEffect" or any of the contained CallEffect (or CallRecursive,
! CallXorEffect) predicates.

! We still need some form of liveness propagation for other relational predicates,
! because there can be intermediate results which are not bound directly in the
! defining stack scopes.

! The theory is that they only flow between Left and Right scope "brackets" though.

! Also, row vars shouldn't need to be included in the scope brackets.  There are no
! relational predicates on row vars right now.

! Akshually, the left and right boundaries of the scopes seem to be defined by the MakeEffect
! and CallEffect stacks with the same row var?

! NOTE: Treat the scope as if the quotation is part of the bracket?
CHR: collect-call-effect-define-scope @ { Live __ } // AS: ?p P{ CallEffect ?q ?a ?b } --
! CHR: collect-call-effect-define-scope @ { Live ?v } // AS: ?p P{ CallEffect ?q ?a ?b } --
! [ ?q ?v in? ]
[ ?q ?a cons :>> ?l ] |
{ Collect ?p } { SubScope ?l ?b } ;


! NOTE: if the stack vars are the same, then we only define a relationship between the vars on top of the stack?
CHR: collect-inline-call-define-scope @ { Live __  } // AS: ?p <={ inline-call-pred __ ?a ?b } -- |
{ Collect ?p }
{ SubScope ?a ?b } ;
! [ ?a lastcdr ?b lastcdr ==
!   [ ?a value-vars ?b value-vars make-imply ]
!   [ { SubScope ?a ?b } ] if ] ;

CHR: collect-iterated @ { Live __ } // AS: ?p <={ Iterated __ { ?i ?b ?c ?d ?o } } -- |
{ Collect ?p }
{ SubScope ?i ?d }
{ SubScope ?d ?o }
{ Scope ?b ?c } ;

CHR: collect-boa-is-a-scope @ { Live __ } // AS: ?p P{ Boa ?c ?i ?o } -- [ ?c ?i cons :>> ?a ] |
{ Collect ?p }
{ SubScope ?a ?o } ;

! NOTE: this is always a same-last-cdr scope.  Shouldn't matter though?
CHR: collect-generic-dispatch-is-scope @ { Live ?l } { Def ?a } { Use ?b } // AS: ?p P{ GenericDispatch ?w ?d ?v ?i ?o } --
[ ?v ?l subset? ] [ ?v ?b subset? ] [ ?d ?l subset? ] [ ?d ?a subset? ] | { Collect ?p } { SubScope ?i ?o } ;

! TODO: Neuralgic example in xor calls with predicates might have disconnected scopes.  In that case, left and right brackets
! might incorrectly be assumed for these "nested" scopes.  Need to check if that is what we need.  Alternatively, assume that these scopes are
! _always_ treated as dividers?  Possibly use the [ declare drop ] approach again if revised scoping rules would correctly
! cover these cases now!  Alternatively, extend the DeclareInstance to be stateful between stacks, or at least connected to them?


! ! TODO: Do we need to keep the paths because we could miss stuff? Probably yes...
! ! ?m: matched set to absorb
! CHR: join-paths @ // { Path ?a ?x ?b } { Path ?c ?y ?d } --
! ! NOTE: need to change that to make sure we're not mixing lefts and rights?
! [ ?b ?c intersect :>> ?m empty? not ]
! [ ?b ?c subset? ?c ?b subset? or ]
! [ ?a ?d intersects? not ]
! ! [ ?a ?y intersects? not ]
! ! [ ?b ?y intersects? not ]
! ! [ ?c ?x intersects? not ]
! ! [ ?d ?x intersects? not ]
! ! [ ?a ?c intersects? not ]
! ! [ ?b ?d intersects? not ]
! [ ?c ?m diff ?a union :>> ?r ]
! [ ?b ?m diff ?d union :>> ?s ]
! [ ?x ?y union ?m union :>> ?p ] | { Path ?r ?p ?s } ;
! ! CHR: redundant-imply @ { Left ?a } { Right ?b } // { Imply ?x ?y } --
! ! [ ?x ?b subset? ] [ ?y ?a subset? ] | ;
! ! CHR: imply-extends-right @ { Imply ?x ?y } // { Right ?b } -- [ ?y ?b subset? ] [ ?x ?b subset? not ]
! ! [ ?x ?b union :>> ?d ] | { Right ?d } ;
! ! CHR: imply-extends-left @ { Imply ?x ?y } // { Left ?b } -- [ ?x ?b subset? ] [ ?y ?b subset? not ]
! ! [ ?y ?b union :>> ?d ] | { Left ?d } ;

: use-def ( left right -- pred )
    [ vars ] bi@ 2dup [ empty? not ] both? [ UseDefs boa ] [ 2drop f ] if ;

! CHR: given-is-given @ { Imply ?a ?b } // { Given ?x } -- [ ?a ?x subset? ] [ ?b ?x subset? not ]
! [ ?b ?x union :>> ?y ] | { Given ?y } ;

! CHR: would-be-defined-by @ { Imply ?a ?b } // { Define ?x } -- [ ?b ?x subset? ] [ ?a ?x subset? not ]
! [ ?a ?x union :>> ?y ] | { Define ?y } ;

! CHR: simple-implication-extends-fringe @ AS: ?p <={ expr-pred } // AS: ?s <={ fringe ?x } --
! [ ?p vars :>> ?v length 1 > ] [ ?v ?x diff :>> ?y length 1 = ] | [ ?s clone [ ?y first suffix ] change-vars ]
! [ ?v ?y diff ?y ?s Left? [ swap ] unless Imply boa ] ;

! ! Desperate Move: Full contagion from both sides...
! CHR: pred-intersects-fringe @ AS: ?p <={ body-pred } // AS: ?s <={ fringe ?x } --
! [ ?p upper-scope-vars vars :>> ?v length 1 > ] [ ?v ?x intersects? ] [ ?v ?x subset? not ] |
! [ ?s clone [ ?v union ] change-vars ] ;

! CHR: pred-connect-right @ AS: ?p <={ body-pred } { Left ?x } { Right ?y } --
! [ ?p upper-scope-vars vars :>> ?v ] [ ?v ?x intersects? not ] [ ?y ?v set-cut :>> ?b [ empty? not ] both? ] |
! {  }

! GENERIC: defines-scope ( pred -- left right )
! M: body-pred defines-scope drop f f ;
! M: CallEffect defines-scope [ in>> ] [ out>> ] bi ;

! CHR: collect-defines-scope @ { Collect ?p } // --
! [ ?p defines-scope [ vars ] bi@ :>> ?b swap :>> ?a [ empty? not ] both? ]
! [ ?a ?b union :>> ?c ] | { Live ?c } { Left ?a } { Right ?b } ;
! PREFIX-RULES: { P{ CompMode } P{ Left __ } P{ Right __ } }
PREFIX-RULES: { P{ CompMode } P{ Live __ } }

! ! This is used so as to not always have to touch Def manually
! CHR: imply-extends-def @ { Imply ?x ?y } // { Def ?l } --
! [ ?x ?l subset? ] [ ?y ?l subset? not ] [ ?y ?l union :>> ?m ] |
! { Def ?m } ;

CHR: have-def-use @ { Def ?l } // { Imply ?x ?y } { Use ?r } --
[ ?y ?r subset? ] [ ?x ?r intersects? not ] [ ?x ?l subset? ]
[ ?r ?x union :>> ?s ] | { Live ?x } { Use ?s } ;



! ** Predicate-speficic Modes and Collection


! *** Relations
! TODO: only add these if it makes sense for optimization?
! CHR: rel-pred-modes @ <={ rel-pred M{ ?x } M{ ?y } } // -- | [ ?x ?y make-imply ] [ ?y ?x make-imply ] ;

! *** Mathematical Operations

! TODO: one of these is possibly never used?
! Nope, seems like we need all of them, or another error with scoping exists?
! CHR: commutative-op-modes @ <={ commutative-op ?z ?x ?y } // -- |
CHR: commutative-op-extend-def @ AS: ?p <={ commutative-op } // { Def ?l } --
[ ?l ?p vars set-cut :>> { ?x ?y } nip length 1 = ]
[ ?l ?y first suffix :>> ?m ] | { Def ?m } [ ?x ?y make-imply ] ;

! CHR: commutative-op-extend-use @ AS: ?p <={ commutative-op } { Def ?l } // { Use ?r } --
! [ ?l ?p vars set-cut :>> { ?x ?y } drop length 2 = ]
! [ ?l ?y first suffix :>> ?m ] | { Def ?m } ;

! |
! [ { ?x ?y } ?z make-imply ]
! [ { ?y ?z } ?x make-imply ]
! [ { ?z ?x } ?y make-imply ]
!     ;

! *** Other expr preds
! NOTE: including the reverse mode here to fix things like [ [ ... ] curry ]
CHR: slot-modes @ { Slot ?o ?n ?v } // { Def ?l } --
[ { ?o ?n } vars ?l subset? ] [ ?v ?l in? not ] [ ?l ?v suffix :>> ?m ]
| { Def ?m } [ { ?o ?n } ?v make-imply ]
! [ { ?v ?n } ?o make-imply ]
    ;

! Desperation Rule to deal with carrying over slot val info to prevent having to use the bidirectional mode above...
! XXX Maybe then the collector can be moved up again?
! CHR: right-slot-vals-are-right @ { Slot ?o ?n ?v } // { Right ?s ?w } -- [ ?o ?w in? ] [ ?v ?w in? not ]
! [ ?w ?v suffix :>> ?b ] | { Live { ?v } } { Right ?s ?b } ;
! TODO: check if this needs to be transitive! yes ( [ [ swap ] curry curry ] )
! PREFIX-RULES: { P{ CompMode } }
CHR: used-tupe-slots-are-used @ { Slot ?o ?n ?v } // { Use ?w } --
! [ { ?o ?n } vars ?l subset? ]
[ ?o ?w in? ] [ ?v ?w in? not ]
[ ?w ?v suffix :>> ?b ] | { Live { ?v } } { Use ?b } ;

! PREFIX-RULES: { P{ CompMode } P{ Live __ } }


! CHR: call-effect-modes @ { CallEffect ?q ?a ?b } // -- |
! ! [ { ?q ?a } ?b make-imply ] ;
! [ { ?q ?a } vars ?b list*>array unclip-last [ vars ] bi@ Path boa ] ;

! ! TODO: maybe abstract scope-pred abstraction?
! CHR: call-effect-modes @ { CallEffect ?q ?a ?b } // -- |
! [ { ?a ?q } ?b make-imply ]
! [ ?a { ?b ?q } make-imply ] ;

! CHR: call-recursive-modes @ <={ simple-call-pred __ ?a ?b } // -- |
! [ ?a ?b make-imply ] ;


! ! *** Effect Instance types

! ! FIXME: prove we are not missing anything by ignoring xor effects here?
! CHR: effect-instance-modes @ { Instance ?x P{ Effect ?a ?b __ __ } } // -- |
! [ { ?a ?x } ?b make-imply ]
! [ ?a { ?b ?x } make-imply ] ;

! ! TODO: need scope here? Right now only assuming that resulting CallEffects from e.g. curry do define scope
! CHR: collect-effect-instance @ { Live ?v } // AS: ?p P{ Instance ?x P{ Effect __ __ __ __ } } --
! [ ?x ?v in? ] | { Collect ?p } ;

! ! *** Iteration construct
! ! TODO: Counters

! CHR: iterated-modes @ { Iterated __ { ?i ?b ?c ?d ?o } } // -- |
! [ ?i ?b make-imply ]
! [ ?c ?d make-imply ] ;

! ! CHR: collect-iterated @ { Live ?v } // AS ?p P{ Iterated __ { ?i ?a ?b ?c ?o } } -- |
! ! [ { ?i ?o } ]

! ! *** Macro-likes
CHR: macro-call-modes @ { MacroCall __ ?a ?q } // -- | [ ?a ?q make-imply ] ;

! CHR: boa-modes @ <={ Boa ?c ?i ?o } // -- | [ { ?c ?i } ?o make-imply ] ;

! GENERIC: expr-modes ( pred -- modes )
! M: rel-pred expr-modes

! CHR: standard-expr-extend-left @ AS: ?p <={ expr-pred } // { Left ?a } --
! [ ?p vars :>> ?v ?a diff :>> ?y ]


! CHR: pred-defines-imply @ { Left ?a } { Right ?b } AS: ?p <={ body-pred } // --
! [ ?p vars :>> ?v length 1 > ] [ ?p dep-pair :>> ?m ]
! [ ?v ?a subset? not ] [ ?v ?b subset? not ]
! [ ?m first ?b diff :>> ?x ] [ ?m second ?a diff :>> ?y ]
! ! [ { [ ?x empty? ] [ ?y empty? ] } 0&& not ]
! | { Imply ?x ?y } ;


! CHR: extend-right-set-from-left @ // { Right ?y } { ImplyLeft ?l ?v } -- [ ?v ?y subset? ]
! [ ?y ?l union :>> ?b ] | { Right ?b } ;

! CHR: extend-left-set-from-right @ // { Left ?y } { ImplyRight ?l ?v } -- [ ?v ?y subset? ]
! [ ?y ?l union :>> ?b ] | { Left ?b } ;

GENERIC: upper-vars ( pred -- vars )
M: val-pred upper-vars vars ;
M: Iterated upper-vars stuff>> [ first vars ] [ last vars ] bi union ;
M: CallEffect upper-vars vars ;
M: CallXorEffect upper-vars [ in>> vars ] [ out>> vars ] bi union ;
M: CallRecursive upper-vars [ in>> vars ] [ out>> vars ] bi union ;
M: Instance upper-vars val>> 1array ;

! TODO: if this is a performance bottleneck, try smarter implementation!
! : maybe-join-vars ( set vars -- vars ? )
!     over '[ unclip-slice _ [ subset? ] [ in? not ] bi-curry bi* and ] find-permutation
!     [ first suffix t ] [ f ] if* ;
! : maybe-join-vars ( set vars -- vars var/f )
!     over diff dup length 1 = [ first [ suffix ] keep ] [ drop f ] if ;

! CHR: live-effect-instance @ { Instance ?x ?e } // { Live ?c } -- [ ?e valid-effect-type? ] [ ?x ?c in? ]
! ! TODO: possibly also use left and right here?
! [ ?c ?e vars union :>> ?d ] | { Live ?d } ;

! CHR: iterated-defines-deps @ { Collect P{ Iterated __ { __ ?b ?c ?d __ } } } // { Live ?a } --
! [ { ?b ?c ?d } vars ?a union :>> ?x ] | { Live ?x } ;

! CHR: live-xor-call @ { CallXorEffect ?tau ?a ?b } // { Live ?c } -- [ { ?a ?b } vars :>> ?x ?c intersects? ]
! [ ?x ?c append ?tau vars union :>> ?d ] | { Live ?d } ;

GENERIC: flow-vars ( pred -- vars )
M: body-pred flow-vars vars ;
M: Iterated flow-vars stuff>> [ first vars ] [ last vars ] bi union ;
UNION: dataflow-pred expr-pred CallEffect GenericDispatch CallRecursive Iterated ;

! CHR: left-leader-is-left @ { Left ?a } // { ImplyLeft ?x ?y } -- [ ?y ?a intersects? ]
! [ ?y ?a diff :>> ?z ] | [ ?z [ f ] [ ?x swap ImplyLeft boa ] if-empty ] ;

! ! TODO: check if we really need both ways.
! CHR: pred-defines-left-join @ AS: ?p <={ dataflow-pred } // { Left ?a } --
! [ ?p flow-vars :>> ?v ?a subset? not ]
! [ ?v ?a intersect :>> ?x empty? not ]
! [ ?v ?a diff :>> ?y empty? not ]
! [ ?a ?y union :>> ?w ]
! ! [ ?a ?w maybe-join-vars [ :>> ?v drop ] dip :>> ?x ]
! ! [ ?x ?w remove :>> ?y ]
! | { Left ?w } { ImplyLeft ?x ?y } ;

! CHR: pred-defines-right-join @ AS: ?p <={ dataflow-pred } // { Right ?a } --
! [ ?p flow-vars :>> ?v ?a subset? not ]
! [ ?v ?a intersect :>> ?x empty? not ]
! [ ?v ?a diff :>> ?y empty? not ]
! [ ?a ?y union :>> ?w ]
! | { Right ?w } { ImplyRight ?x ?y } ;

;
