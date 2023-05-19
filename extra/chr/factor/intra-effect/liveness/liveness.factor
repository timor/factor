USING: accessors arrays assocs chr.factor chr.parser chr.state classes.tuple
grouping kernel lists math.combinatorics sequences sequences.extras sets terms
types.util ;

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

CHR: flatten-live-set @ // AS: ?p <={ Live ?s } -- [ ?s [ cons-state? ] any? ] |
[ ?p clone ?s vars >>vars ] ;

PREFIX-RULES: { P{ CompMode } }

! ** Normalization
CHR: unique-dep @ { Dep ?x ?y } // { Dep ?x ?y } -- | ;
CHR: same-rel @ { Rel ?x ?y ?v } // { Rel ?x ?y ?w } -- [ ?v ?w set= ] | ;
CHR: non-dep @ // { Dep ?x ?x } -- | ;
CHR: same-live-set @ { Live ?x } // { Live ?y } -- [ ?x ?y set= ] | ;
CHR: symmetric-dep @ { Dep ?x ?y } // { Dep ?y ?x } -- | ;

! Holding off generating these until finished reasoning, to allow disappearing constraints
! to take their deps with them!
PREFIX-RULES: { P{ CompMode } P{ Roots __ } }
! ** Collecting pairwise dependencies
! CHR: rel-pred-live-deps @ <={ rel-pred M{ ?x } M{ ?y } } // -- { Dep ?x ?y } { Dep ?y ?x } ;
CHR: binary-rel-pred-live-deps @ AS: ?p <={ expr-pred } // -- [ ?p vars >array :>> ?v length 2 = ]
[ ?v first2 :>> ?x drop :>> ?y ] |
{ Dep ?x ?y } ;

! TODO: expand to n-ary predicates via combinatorial explosion?
CHR: ternary-expr-pred-live-deps @ AS: ?p <={ expr-pred } // -- [ ?p vars >array :>> ?v length 3 = ] |
[ ?v 2 all-combinations [ Dep slots>tuple ] map ] ;

CHR: call-effect-live-deps @ <={ CallEffect ?q ?i ?o } // -- |
[ ?i vars [ ?q Dep boa ] map
  ?o vars [ ?q Dep boa ] map append ] ;

! TODO: Check Whether we need intra-input or intra-output deps also
! TODO: expand to other call-like preds
! NOTE: seems we might not need intra-input or intra-output, but
! relations with the row vars?
! TODO: somewhat sure that this also needs to be done for callrecursive, maybe even
! call-effect ;
CHR: call-xor-effect-live-deps @ { CallXorEffect __ ?a ?b } // --
[ ?a vars :>> ?i ?b vars :>> ?o
  ! intersect :>> ?c
  2drop t
] |
! [ ?i ?c diff ?o ?c diff [ Dep boa ] cartesian-map concat ] ;
[ ?i ?o [ Dep boa ] cartesian-map concat ] ;

CHR: call-recursive-live-deps @ { CallRecursive __ ?a ?b } // --
[ ?a vars :>> ?i ?b vars :>> ?o
  intersect :>> ?c ] |
[ ?i ?c diff ?o ?c diff [ Dep boa ] cartesian-map concat ] ;

! TODO: Does this apply to all value preds with their rest slots?  The idea is to only include the deps which allow
! to conclude unique information
CHR: slot-live-deps-val @ { Slot ?o ?n M{ ?v } } // -- | { Dep ?o ?v } ;
CHR: slot-live-deps-slot @ { Slot ?o M{ ?n } ?v } // -- | { Dep ?o ?n } ;

CHR: iteration-deps @ { Iterated __ ?s } // --
[ ?s sequence? ] |
! FIXME: that explicit lift here is because the ground value won't be present when reasoning
! inside the eq-disjoint-set scope.
[ ?s f lift [ list*>array ] map 2 <clumps> [ first2 zip ] map-concat
  [ Dep slots>tuple ] map
] ;

! ** Building the chains
PREFIX-RULES: { P{ CompMode } }

CHR: start-in-rel @ { Dep ?x ?y } { Roots ?v } // -- [ ?x ?v in? ] [ ?y ?v in? not ] | { Rel ?x ?y { } } ;
CHR: start-out-rel @ { Dep ?x ?y } { Roots ?v } // -- [ ?x ?v in? not ] [ ?y ?v in? ] | { Rel ?x ?y { } } ;

CHR: merge-rel-from @ <={ Live ?l } { Rel ?x ?y ?v } // { Rel ?a ?y ?w } -- [ ?x ?l in? ] [ ?a ?l in? ] [ ?w ?v set= ] | ;
CHR: merge-rel-to @ <={ Live ?l } { Rel ?x ?y ?v } // { Rel ?x ?z ?w } -- [ ?y ?l in? ] [ ?z ?l in? ] [ ?w ?v set= ] | ;


! NOTE: making them all bidirectional for now...
CHR: grow-rel-forward-1 @ { Dep ?y ?z } { Roots ?r } { Rel ?x ?y ?v } // -- [ ?z ?v in? not ] [ ?y ?r in? not ] [ ?z ?x == not ]
[ ?v ?y suffix :>> ?w ] | { Rel ?x ?z ?w } ;
CHR: grow-rel-forward-2 @ { Dep ?z ?y } { Roots ?r } { Rel ?x ?y ?v } // -- [ ?z ?v in? not ] [ ?y ?r in? not ] [ ?z ?x == not ]
[ ?v ?y suffix :>> ?w ] | { Rel ?x ?z ?w } ;

CHR: grow-rel-backward-1 @ { Dep ?a ?x } { Roots ?r } { Rel ?x ?y ?v } // -- [ ?a ?v in? not ] [ ?x ?r in? not ] [ ?a ?y == not ]
[ ?v ?x prefix :>> ?w ] | { Rel ?a ?y ?w } ;
CHR: grow-rel-backward-2 @ { Dep ?x ?a } { Roots ?r } { Rel ?x ?y ?v } // -- [ ?a ?v in? not ] [ ?x ?r in? not ] [ ?a ?y == not ]
[ ?v ?x prefix :>> ?w ] | { Rel ?a ?y ?w } ;

! CHR: have-live-in-out-rel @ { Rel ?x ?y ?v } { In ?a } { Out ?b } // -- [ ?v empty? not ]
! [ ?x ?a in? ] [ ?y ?b in? ] | { Live ?v } ;

CHR: have-live-root-root-rel @ { Rel ?x ?y ?v } { Roots ?a } // -- [ ?v empty? not ]
[ ?x ?a in? ] [ ?y ?a in? ] | { Live ?v } ;
! ! Assumption: if we hit the live set from the roots, then we will hit the root set eventually
! CHR: have-live-root-rel @ { Rel ?x ?y ?v } { Roots ?a } // -- [ ?v empty? not ]

! CHR: have-live-out-out-rel @ { Rel ?x ?y ?v } { Out ?a } // -- [ ?v empty? not ]
! [ ?x ?a in? ] [ ?y ?a in? ] | { Live ?v } ;

! CHR: have-live-other-rel @ { Rel ?x ?y ?v } <={ Live ?a } <={ Live ?b } // -- [ ?v empty? not ]
! [ ? ]

! CHR: live-rel-pred-start @ <={ rel-pred M{ ?x } M{ ?y } } { In ?v } // -- [ ?x ?v in? ] | { Dep ?x ?y } ;
! CHR: live-rel-pred-2 @ <={ rel-pred M{ ?y } M{ ?x } } { In ?v } // -- [ ?x ?v in? ] | { Dep ?x ?y } ;

! CHR: live-rel-pred-out-1 @ <={ rel-pred M{ ?x } M{ ?y } } { Out ?v } // -- [ ?x ?v in? ] | { Dep ?x ?y } ;
! CHR: live-rel-pred-out-2 @ <={ rel-pred M{ ?y } M{ ?x } } { Out ?v } // -- [ ?x ?v in? ] | { Dep ?x ?y } ;

CHR: live-set-join @ // { Live ?k } { Live ?l } -- [ ?k ?l union :>> ?m ] |
{ Live ?m } ;
! [ { ?k } ?c slots>tuple ] ;
! { ?c ?k } ;


;
