USING: accessors arrays chr.factor chr.parser combinators.short-circuit kernel
math sequences sets terms ;

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

PREFIX-RULES: { P{ CompMode } }
! "Liveness Anchor"
GENERIC: upper-scope-vars ( pred -- term )
M: expr-pred upper-scope-vars ;
M: val-pred upper-scope-vars val>> ;
M: LoopVar upper-scope-vars stuff>> first ;
M: Iterated upper-scope-vars stuff>> [ first ] [ last ] bi 2array ;
M: CallEffect upper-scope-vars ;
M: CallRecursive upper-scope-vars ;
M: CallXorEffect upper-scope-vars [ in>> ] [ out>> ] bi 2array ;
M: MacroCall upper-scope-vars ;


UNION: merging-set Given Define ;

! CHR: merge-liveness-set @ // AS: ?a <={ merging-set ?x } AS: ?b <={ merging-set ?y } --
! [ ?a ?b [ class-of ] same? ] | [ ?x ?y union 1array ?a class-of slots>tuple ] ;

! CHR: have-live @ { Given ?x } { Define ?y } // { Live ?v } -- [ ?x ?y intersect :>> ?z empty? not ]
! [ ?z ?v subset? not ]
! [ ?z ?v union :>> ?a ] [ ?y ?z ]
! |
CHR: already-live @ { Live ?x } // { Live ?y } -- [ ?y ?x subset? ] | ;
CHR: merge-live @ // { Live ?x } { Live ?y } -- [ ?x ?y union :>> ?z ] | { Live ?z } ;

! ** Predicate-independent handling
! CHR: body-pred-is-covered @ { Left ?a } { Right ?b } // AS: ?p <={ body-pred } --
CHR: body-pred-is-covered @ { Live ?a } // AS: ?p <={ body-pred } --
! CHR: body-pred-is-covered @ { Given ?x } { Define ?y } // AS: ?p <={ body-pred } --
! [ ?p upper-scope-vars vars :>> ?v ] [ ?v ?a subset? ] ! [ ?v ?b subset? ]
[ ?p upper-scope-vars vars :>> ?v ] [ ?v ?a subset? ] ! [ ?v ?b subset? ]
! [ ?p vars :>> ?v ] [ ?v ?a subset? ] ! [ ?v ?b subset? ]
| { Collect ?p } ;


! CHR: param-is-live @ { Left ?a } { Right ?b } // { Live ?c } -- [ ?a ?b intersect :>> ?x ?c subset? not ]
! [ ?c ?x union :>> ?d ] | { Live ?d } ;

! misnomer...
! usually used as ( existing possible-extension -- things-connecting-it new-things )
: set-xor ( set1 set2 -- common in-set-2-but-not-set-1 )
    members [ swap in? ] with partition ;

CHR: circular-path @ // { Path ?a ?m ?b } -- [ ?a ?b intersects? ] | [ { ?a ?m ?b "circular path" } throw ] ;
CHR: defunct-path @ // { Path ?a ?m ?b } -- [ ?a ?m intersects? ?b ?m intersects? or ] | [ { ?a ?m ?b "malformed path" } throw ] ;

! CHR: duplicate-imply @ { Imply ?x ?y } // { Imply ?x ?y } -- | ;
CHR: duplicate-imply @ { Path ?x ?v ?y } // { Path ?x ?v ?y } -- | ;
CHR: subsume-path @ { Path ?a ?m ?b } // { Path ?c ?n ?d } -- [ ?a ?c set= ] [ ?n ?m subset? ] [ ?b ?d set= ] | ;

CHR: impossible-path-left @ { Left ?x } // { Path __ __ ?b } -- [ ?b ?x intersects? ] | ;
CHR: impossible-path-right @ { Right ?x } // { Path ?a __ __ } -- [ ?a ?x intersects? ] | ;

CHR: have-complete-path @ { Left ?x } { Right ?y } { Path ?a ?m ?b } // --
[ ?a ?x subset? ] [ ?b ?y subset? ] | { Live ?m } ;

! TODO: Do we need to keep the paths because we could miss stuff? Probably yes...
! ?m: matched set to absorb
CHR: join-paths @ { Path ?a ?x ?b } { Path ?c ?y ?d } // -- [ ?b ?c intersect :>> ?m empty? not ]
[ ?a ?d intersects? not ]
[ ?a ?y intersects? not ]
[ ?b ?y intersects? not ]
[ ?c ?x intersects? not ]
[ ?d ?x intersects? not ]
! [ ?a ?c intersects? not ]
! [ ?b ?d intersects? not ]
[ ?c ?m diff ?a union :>> ?r ]
[ ?b ?m diff ?d union :>> ?s ]
[ ?x ?y union ?m union :>> ?p ] | { Path ?r ?p ?s } ;
! CHR: redundant-imply @ { Left ?a } { Right ?b } // { Imply ?x ?y } --
! [ ?x ?b subset? ] [ ?y ?a subset? ] | ;
! CHR: imply-extends-right @ { Imply ?x ?y } // { Right ?b } -- [ ?y ?b subset? ] [ ?x ?b subset? not ]
! [ ?x ?b union :>> ?d ] | { Right ?d } ;
! CHR: imply-extends-left @ { Imply ?x ?y } // { Left ?b } -- [ ?x ?b subset? ] [ ?y ?b subset? not ]
! [ ?y ?b union :>> ?d ] | { Left ?d } ;

: make-imply ( left right -- pred )
    ! [ vars ] bi@ 2dup [ empty? not ] both? [ Imply boa ] [ 2drop f ] if ;
    [ vars ] bi@ 2dup [ empty? not ] both? [ f swap Path boa ] [ 2drop f ] if ;

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
! [ ?p upper-scope-vars vars :>> ?v ] [ ?v ?x intersects? not ] [ ?y ?v set-xor :>> ?b [ empty? not ] both? ] |
! {  }

GENERIC: defines-scope ( pred -- left right )
M: body-pred defines-scope drop f f ;
M: CallEffect defines-scope [ in>> ] [ out>> ] bi ;

! CHR: collect-defines-scope @ { Collect ?p } // --
! [ ?p defines-scope [ vars ] bi@ :>> ?b swap :>> ?a [ empty? not ] both? ]
! [ ?a ?b union :>> ?c ] | { Live ?c } { Left ?a } { Right ?b } ;

PREFIX-RULES: { P{ CompMode } P{ Left __ } P{ Right __ } }

! ** Predicate-speficic Modes and Collection

! *** Relations
! TODO: only add these if it makes sense for optimization?
CHR: rel-pred-modes @ <={ rel-pred ?x ?y } // -- | [ ?x ?y make-imply ] [ ?y ?x make-imply ] ;

! *** Mathematical Operations

! TODO: one of these is possibly never used?
CHR: binop-modes @ <={ binop ?z ?x ?y } // -- |
[ { ?x ?y } ?z make-imply ]
[ { ?y ?z } ?x make-imply ]
[ { ?z ?x } ?y make-imply ] ;

! *** Other expr preds
CHR: slot-modes @ { Slot ?o ?n ?v } // -- | [ { ?o ?n } ?v make-imply ] ;


! *** CallEffect and friends

CHR: call-effect-modes @ { CallEffect ?q ?a ?b } // -- | [ { ?q ?a } ?b make-imply ] ;

! ! TODO: maybe abstract scope-pred abstraction?
! CHR: call-effect-modes @ { CallEffect ?q ?a ?b } // -- |
! [ { ?a ?q } ?b make-imply ]
! [ ?a { ?b ?q } make-imply ] ;

UNION: simple-call-pred CallRecursive CallXorEffect ;
CHR: call-recursive-modes @ <={ simple-call-pred __ ?a ?b } // -- |
[ ?a ?b make-imply ] ;


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

CHR: boa-modes @ <={ Boa ?c ?i ?o } // -- | [ { ?c ?i } ?o make-imply ] ;

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
