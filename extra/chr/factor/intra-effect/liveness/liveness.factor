USING: accessors arrays chr.factor chr.factor.util chr.parser classes.tuple
kernel lists sequences sequences.generalizations sets terms ;

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

PREFIX-RULES: { P{ Liveness } }
! ** Live set hous-keeping
UNION: merging-set Def Use Live ;

! NOTE: this is for catching the case where we perform additional stack unification during live set
! reasoning
CHR: malformed-liveness-set @ // AS: ?a <={ merging-set ?x } -- [ ?x [ term-var? ] all? not ] |
[ { ?a "malformed-liveness-set" } throw ] ;

: valid-live-set? ( x -- ? ) [ term-var? ] all? ;

! TODO: check whether removing the subsumption rule is actually faster overall?
! CHR: normalize-use-set @ // { Use ?x } -- [ ?x valid-live-set? not ] [ ?x vars :>> ?y ] | { Use ?y } ;
CHR: subsume-use-set @ { Use ?x } // { Use ?y } -- [ ?y ?x subset? ] | ;
CHR: merge-use-set @ // { Use ?x } { Use ?y } -- [ ?x ?y union :>> ?z ]
| { Use ?z } ;

CHR: new-scope @ // <={ Scope ?i ?o } -- [ ?i vars ?o vars union :>> ?v ] |
{ Use ?v } ;

! ** Dependency Generation
! *** Unconditional
UNION: call-pred CallRecursive CallEffect CallXorEffect PrimCall GenericDispatch ;
GENERIC: pred-scopes ( pred -- preds )
M: body-pred pred-scopes drop f ;
M: call-pred pred-scopes [ in>> ] [ out>> ] bi SubScope boa ;
M:: Iterated pred-scopes ( pred -- preds )
    pred tuple-slots rest 5 firstn :> ( i b c d o )
    { P{ SubScope i d }
      P{ SubScope d o }
      P{ Scope b c }
    } ;
M: Boa pred-scopes
    [ spec>> ] [ in-stack>> cons ] [ out-stack>> ] tri SubScope boa ;

CHR: body-pred-scopes @ AS: ?p <={ body-pred } // -- [ ?p pred-scopes :>> ?l ] | [ ?l ] ;

! *** Conditional

CHR: used-val-of-val-pred-uses-args @ AS: ?p <={ val-pred ?x . ?r } { Use ?v } // -- [ ?x ?v in? ] [ ?r vars :>> ?y empty? not ] |
{ Use ?y } ;

! Special case for the above since LocOp is not a val-pred, but if the slot is used, the item is used too
CHR: used-loc-uses-item @ <={ LocOp ?x __ ?i . ?r } { Use ?v } // -- [ ?x ?v in? ] [ ?i vars :>> ?y ] |
{ Use ?y } ;

CHR: unique-implication @ { Imply ?a ?b } // { Imply ?c ?d } -- [ ?a ?c set= ] [ ?b ?d set= ] | ;

CHR: redundant-implication @ { Use ?v } // { Imply __ ?b } -- [ ?b ?v subset? ] | ;

! TODO: need to keep the implications? -> shouldnt, because they couldn't add new info anyways?
CHR: independent-implication-match @ // { Imply ?a ?b } { Imply ?c ?d } -- [ ?a ?c intersects? not ] [ ?b ?d set= ]
[ ?a ?c union ?b union :>> ?v ] ! These could be "corollaries" in ?a and ?c
| { Use ?v } ;

! TODO: Really make sure why or why not it is necessary to keep or not keep the partial one here, and if so, which?
CHR: combine-implications @ // { Imply ?a ?b } { Imply ?c ?d } -- [ ?a ?c intersects? not ] [ ?b ?d subset? ]
[ ?a ?c union :>> ?x ]
[ ?d ?b diff :>> ?y ] |
{ Imply ?x ?y } ;

! Set of vars of a body pred which means it is fully defined
GENERIC: expression-vars ( pred -- set )
M: body-pred expression-vars drop f ;
M: expr-pred expression-vars vars ;
! Keep non-equating relations between variables only if determined to be live another way
M: Le expression-vars drop f ;
M: Neq expression-vars drop f ;
M: Cloned expression-vars
    [ cloned-val>> ] [ orig-val>> ] bi 2array ;
M: LocOp expression-vars
    [ loc>> ] [ item>> ] bi [ vars ] bi@ union ;
! Slot def-use reasoning is not symmetric, becoming apparent in
! [ curry uncurry ], leaving dead unreachable info.
! Does this apply to locations as well? -> Test with curry uncurry example on mutable locs!
! at least removing the following bidirectional slot rule also fixes those..
! M: Slot expression-vars vars ;

CHR: imply-body-pred-could-define @ AS: ?p <={ body-pred } { Use ?v } // --
[ ?p expression-vars :>> ?x ]
[ ?x ?v [ in? ] curry partition :>> { ?a ?b } [ empty? not ] both? ] |
{ Imply ?a ?b } ;

! NOTE: this is also a partial subset problem???
CHR: imply-body-pred-could-extend @ AS: ?p <={ body-pred } { Use ?v } // { Imply ?c ?d } --
[ ?p expression-vars :>> ?l ?v intersects? not ]
[ ?l ?d [ in? ] curry partition :>> { ?a ?b } [ empty? not ] both? ]
[ ?b ?c subset? not ]
[ ?c ?a union :>> ?x ]
[ ?d ?a diff ?b union :>> ?y ]
|
{ Imply ?x ?y } ;

! Hole matching of "directional" predicates, where it matters what stuff is known and
! what is unknown!
GENERIC: directed-vars ( pred -- ante conse )
M: body-pred directed-vars drop f f ;
M: Slot directed-vars
    [ val>> ] [ n>> ]
    [ loc>> ] tri
    [ drop 2array vars ] 2keep
    2array vars ;

CHR: directed-imply-could-define @ AS: ?p <={ body-pred } { Use ?v } // --
[ ?p directed-vars :>> { ?x ?y } [ empty? not ] both? ]
[ ?x ?v intersect ?y ?v diff :>> { ?a ?b } [ empty? not ] both? ] |
{ Imply ?a ?b } ;

! NOTE: at least for [ 1array (clone) ] this needs to keep the original implication in tact
! to make sure that other slot preds have the chance to close the chain correctly!
! CHR: directed-imply-could-extend @ AS: ?p <={ body-pred } { Use ?v } // { Imply ?c ?d } --
CHR: directed-imply-could-extend @ AS: ?p <={ body-pred } { Use ?v } { Imply ?c ?d } // --
[ ?p directed-vars :>> { ?x ?y } [ empty? not ] both? ]
[ ?x ?v intersects? not ]
[ ?x ?d intersect ?y ?d diff :>> { ?a ?b } [ empty? not ] both? ]
[ ?b ?c subset? not ]
[ ?c ?a union :>> ?r ]
[ ?d ?a diff ?b union :>> ?s ]
|
{ Imply ?r ?s } ;

! Special case: Retain stack values are always used
CHR: use-retain-stack-values @ AS: ?p <={ LocOp R __ ?v . __ } // -- [ ?v vars :>> ?x ] |
{ Use ?x } ;

! ** Collection

PREFIX-RULES: { P{ Collection } }
! "Liveness Anchor"
GENERIC: upper-scope-vars ( pred -- term )
M: body-pred upper-scope-vars ;
M: Cloned upper-scope-vars [ cloned-val>> ] [ orig-val>> ] bi 2array ;
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
M: Iterated upper-scope-vars drop { } ;

CHR: collect-covered-body-pred @ { Use ?a } // AS: ?p <={ body-pred } --
[ ?p upper-scope-vars [ vars :>> ?v drop ] keep ] ! [ ?v empty? not ]
[ ?v ?a subset? ] |
{ Collect ?p } ;

;
