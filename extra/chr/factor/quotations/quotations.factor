USING: accessors arrays chr chr.factor chr.factor.defs chr.factor.effects
chr.factor.terms chr.parser chr.state classes.algebra combinators
combinators.short-circuit continuations effects generic kernel lists math
math.parser quotations sequences sets strings terms types.util words
words.symbol ;

IN: chr.factor.quotations
FROM: syntax => _ ;
FROM: chr => val-pred ;
FROM: chr.factor.terms => Call ;
FROM: chr.factor.types => Instance ;
FROM: chr.factor.effects => Effect ;

! * Quotation Inference

GENERIC: elt>var ( i elt -- obj )
M: f elt>var drop number>string "v" prepend utermvar ;
M: string elt>var nip utermvar ;
M: pair elt>var
    first2 drop elt>var ;

: elt-vars ( seq -- seq )
    [ swap elt>var ] map-index ;
! [ swap dup pair? [ first ] when
!   [ nip ] [ number>string "v" prepend ] if*
!   uvar
!   <term-var>
! ] map-index <reversed> ;

: effect>stack-elts ( effect -- lin lout )
    [ in>> elt-vars <reversed> >list ]
    [ out>> elt-vars <reversed> >list ] bi ;

:: add-row-vars ( lin lout effect -- lin lout )
    effect [ in-var>> ] [ out-var>> ] bi
    [ dup [ utermvar ] when ] bi@
    :> ( i o )
    { { [ i o [ not ] both? ]
        [ "rho" utermvar :> rho
          lin rho list*
          lout rho list* ] }
      { [ i o [  ] both? ]
        [ lin i list*
          lout o list* ] }
      [ lin __ list* lout __ list* ]
    } cond ;

: shuffle-effect>stacks ( effect -- lin lout )
    [ in>> elt-vars ]
    [ dupd shuffle ] bi
    [ <reversed> >list ] bi@
    "rho" utermvar [ lappend ] curry bi@ ;

: effect>stacks ( effect -- lin lout )
    [ effect>stack-elts ]
    [ add-row-vars ] bi ;

:: shuffle-rules ( in out effect -- preds )
    effect effect>stacks :> ( sin sout )
    sin list>array* <reversed> :> vin
    sout list>array* <reversed> :> vout
    sin lastcdr :> rho
    sout lastcdr :> sig
    effect shuffle-mapping
    [| ni no | no vout nth ni vin nth Is boa ] map-index
    Is{ sig rho } suffix
    Is{ sin in } prefix
    Is{ out sout } suffix
    vin dup effect shuffle diff [ Drop boa suffix ] each
    ;


PREDICATE: quot-sym < word "quot-id" word-prop? ;
: <quot-sym> ( name -- word ) usym dup t "quot-id" set-word-prop ;
! PREDICATE: callable-word < word { [ symbol? not ] [ quot-sym? not ] } 1&& ;
PREDICATE: callable-word < word { [ symbol? not ] } 1&& ;



TUPLE: Transeq < chr-pred label from to quot ;
TUPLE: Trans < chr-pred from to command ;
<PRIVATE
TUPLE: QueueTrans < chr-pred label from to command ;
TUPLE: BuildQuot < chr-pred from to quot ;
TUPLE: TransQueue < chr-pred label preds ;
TUPLE: InferredQuot < chr-pred var quot in out ;
PRIVATE>
TUPLE: BuildNamedQuot < BuildQuot var ;
TUPLE: Mark < chr-pred ctx val ;
TUPLE: Marked < chr-pred vals ;

TUPLE: InferWord < chr-pred word ;
TUPLE: InferQuot < chr-pred var code ;


! PREDICATE: callable-word < word symbol? not ;

! ** Value-based, no transition step
GENERIC: build-expr ( in-stack item -- expr )
M: callable-word build-expr swap Ev boa ;
M: object build-expr <wrapper> swons ;
GENERIC: build-quot-step ( stack word -- stack expr )
M: object build-quot-step ( stack word -- stack expr )
    build-expr
    "s" utermvar [ swap Is boa ] keep swap ;

:: known-effect-stacks ( sin sout w -- chrs )
    w defined-effect :> e
    e effect>stack-elts :> ( in out )
    in "a" utermvar dup :> a lappend :> in
    out "b" utermvar dup :> b lappend :> out
    [ { sin sout } { in out } ==! ] 1array
    e bivariable-effect? [ Is{ b a } suffix ] unless ;

M: callable-word build-quot-step
    [ call-next-method ]
    ! stack-out expr stack-in word
    [ [ pick ] dip known-effect-stacks ] 2bi swap suffix ;

: build-quot-body ( stack-in stack-out quot -- res )
    swapd [ build-quot-step ] { } map-as
    [ Is boa ] dip swap suffix ;

! : build-quot-expr ( quot -- res )
!     "a" utermvar "b" utermvar
!     [ rot dup word? [ def>> ] when build-quot-body ]
!     [ Effect new swap >>out swap >>in swap >>word ] 3bi suffix
!     ;

:: build-quot-expr ( quot -- res )
    P{ InferWord quot }
    1array
    ;
    ! "a" utermvar :> in
    ! "b" utermvar :> out
    ! Is{ out { call quot in } }
    ! P{ InferEffect quot f in out f }
    ! 2array ;

TERM-VARS: Quot ;

M:: callable build-quot-step ( stack quot -- stack expr )
    "a" utermvar "b" utermvar :> ( a b )
    a b quot build-quot-body
    "Q" utermvar :> q
    Effect new a >>in b >>out q >>word suffix
    "s" utermvar [ q stack cons Is boa suffix ] keep swap
    q quot Is boa suffix
    ;

M:: \ if build-quot-step ( stack word -- stack expr )
    stack "s" utermvar
    [ [ ? call ] build-quot-body ] keep swap ;


! : build-new-quot ( quot -- res )
!     dup infer build-quot-expr ;

CHRAT: chr-quot { }

! CHR: substitute-if @ // { Is ?b { call A{ ?q } ?a } } -- [ ?q callable? ] [ ?q first \ if eq? ] |
! [| | [ ? call ] ?q rest compose :> cont
! Is{ ?b { call cont ?a } }
! ] ;

CHR: eval-quot-step @ // { Is ?b { call A{ ?q } ?a } } -- [ ?q callable? ] |
[| | ?q empty? [ P{ Is ?b ?a } ]
 [
     ?q unclip-last :> ( rest last )
     {
         P{ Is ?s { call rest ?a } }
         P{ Is ?b { execute last ?s } }
     }
 ] if
] ;

! CHR: literal-quot-call @ { Is ?p A{ ?q } } // Is{ ?b { call ?p ?a } } -- |
! Is{ ?b { call ?q ?a } } ;


! ** Pushing quotations
CHR: execute-push-quot @ // Is{ ?b { execute A{ ?v } ?a } } -- [ ?v callable? ] |
Is{ ?xs ?a }
Is{ ?b L{ Quot . ?xs } }
Is{ Quot ?v }
{ InferQuot Quot ?v } ;


! ** Push literals

CHR: execute-push @ // Is{ ?b { execute A{ ?v } ?a } } -- [ ?v callable-word? not ] |
{ Is ?xs ?a }
{ Is ?b L{ W{ ?v } . ?xs } } ;

! ** Catch primitives
CHR: convert-primitive-exec @ // Is{ ?b { execute A{ ?w } ?a } } -- [ ?w primitive? ] |
{ Is ?b { ?w ?a } } ;

! ** Handle known shuffles
CHR: apply-primitive-shuffle @ // Is{ ?b { A{ ?w } ?a } } -- [ ?w "shuffle" word-prop :>> ?e ] |
[| |
 ?a ?b ?e shuffle-rules
    ! ?e shuffle-effect>stacks :> ( in out )
    ! {
    !     Is{ in ?a }
    !     Is{ ?b out }
    ! }
] ;

! ** Early special words
! CHR: execute-call @ Is{ ?p A{ ?q } } // Is{ ?b { execute call L{ ?p . ?a } } } -- |
! Is{ ?b { call ?q ?a } } ;

! Is{ ?b { call ?p } } ;

! { Call ?p ?rho ?sig }
!     ;

! CHR: mux-call @ // Is{ ?b { execute ? ?a } } -- |
! Is{ L{ ?q ?p ?c . ?rho } ?a }
! Is{ ?b L{ ?v . ?rho } }
! { C True{ ?c } Is{ ?v ?p } }
! { C False{ ?c } Is{ ?v ?q } }
! Is{ ?b { ? ?a } }
!     ;

! ** Handle other effects
CHR: known-effect-structure @ Is{ ?b { execute A{ ?w } ?a } } // -- [ ?w defined-effect :>> ?e ] |
[| | ?e effect>stacks :> ( sin sout )
 {
     Is{ sin ?a }
     Is{ ?b sout }
 }
] ;

ERROR: imbalanced-branch-stacks a b ;
! ** Special words
! CHR: do-branch @ Is{ ?b { if L{ ?q ?p ?c . ?a } } } // -- |
! Is{ ?x { call L{ ?p . ?a } } }
! Is{ ?y { call L{ ?q . ?a } } }
! [ { ?a ?x } { ?a ?y } [ [ solve-eq ] no-var-restrictions ]
!   [ dup recursive-term-error? [ drop f lift imbalanced-branch-stacks ] [ rethrow ] if ] recover
!   drop f
! ]
! { C True{ ?c } Is{ ?b ?x } }
! { C False{ ?c } Is{ ?b ?y } } ;

! CHR: do-mux @ Is{ L{ ?v . ?b } { ? L{ ?q ?p ?c . ?a } } } // -- |
! { Is ?b ?a }
! { <--> True{ ?c } P{ Instance ?c not{ POSTPONE: f } } }
! { <--> False{ ?c } Is{ ?c W{ f } } }
! { C True{ ?c } Is{ ?v ?p } }
! { C False{ ?c } Is{ ?v ?q } }
!     ;

! CHR: expand-if @ { Is ?b { if L{ ?q ?p ?c . ?a } } } // -- |
! { <--> True{ ?c } P{ Instance ?c not{ POSTPONE: f } } }
! { <--> False{ ?c } Is{ ?c W{ f } } }
! { C True{ ?c } { Is{ ?b { call L{ ?p . ?a } } } } }
! { C False{ ?c } { Is{ ?b { call L{ ?q . ?a } } } } } ;

: check-branch-effects ( pair1 pair2 -- )
    [ solve-in-context drop ]
    [ dup recursive-term-error? [ drop [ ground-value-in-context ] bi@ imbalanced-branch-stacks ] [ rethrow ] if ]
    recover ;

! NOTE: pre-computing the branches without conditions does not work because of
! side-effects which have to be assigned to the corresponding conditions!
CHR: expand-if @ { Is ?b { if L{ ?q ?p ?c . ?a } } } // -- |
{ C True{ ?c } { P{ Drop ?q } P{ Instance ?c not{ POSTPONE: f } } } }
{ C False{ ?c } { P{ Drop ?p } Is{ ?c W{ f } } } }
! { C True{ ?c } Is{ ?b { call L{ ?p . ?a } } } }
! { C False{ ?c } Is{ ?b { call L{ ?q . ?a } } } }
{ C True{ ?c } Is{ ?x { call L{ ?p . ?a } } } }
{ C False{ ?c } Is{ ?y { call L{ ?q . ?a } } } }
[ { ?a ?x } { ?a ?y }
  check-branch-effects f
  ! break [ ground-value-in-context ] bi@ [ solve-eq ] no-var-restrictions drop f
]
{ C True{ ?c } Is{ ?b ?x } }
{ C False{ ?c } Is{ ?b ?y } }
    ;

CHR: predicate-words @ Is{ L{ ?c . __ } { A{ ?w } L{ ?v . __ } } } // -- [ ?w "predicating" word-prop :>> ?tau ] [ ?tau class-not :>> ?sig ] |
{ C True{ ?c } { Is{ ?c W{ t } } P{ Instance ?v ?tau } } }
{ C False{ ?c } { Is{ ?c W{ f } } P{ Instance ?v ?sig } } }
;

! ** Handle general word calls

CHR: apply-known-effect @ AS: ?e P{ Effect ?w ?c ?s ?t ?k } Is{ ?b { ?w ?a } } // -- |
[| | ?e instantiate-effect
 [ in>> ] [ out>> ] [ constraints>> ] tri :> ( in out body )
 Is{ in ?a }
 Is{ ?b out }
 body 3array ] ;

! ** Recursive Call Site
TUPLE: RecursiveExec < chr-pred stack-in stack-out word ;

! CHR: request-recursive-effect @ { InferWord ?w } // Is{ ?b { execute A{ ?w } ?a } } -- |
! { RecursiveExec ?a ?b ?w }
! Is{ ?b { ?w ?a } } ;

! ** Make Expression from Execute

! Step one: interpret words as functions from stacks to stacks
CHR: convert-exec-expr @ // Is{ ?b { execute A{ ?w } ?a } } -- |
Is{ ?b { ?w ?a } } ;

! Step two: Convert normal words with only one output parameter
CHR: shave-of-term-expr @ Is{ L{ ?y . __ } { A{ ?w } ?a } } // --
! CHR: shave-of-term-expr @ // Is{ L{ ?y . __ } { A{ ?w } ?a } } --
[ ?w inline? not ] [ ?w defined-effect :>> ?e ]
[ ?e variable-effect? not ]
[ ?e out>> length 1 = ]
[ ?a list>array* :>> ?xs length ?e in>> length :>> ?l >= ]
[ ?xs ?l head :>> ?x  ]
|
{ Expr ?y { ?w ?x } } ;

PREDICATE: predicate-word < word "predicating" word-prop ;

! ** Folding
GENERIC: fold-word? ( w -- ? )
M: object fold-word? drop f ;
M: predicate-word fold-word? drop t ;
M: word fold-word? foldable? ;

! NOTE: fold errors are silent here
! FIXME: do this converstion completely, without using Expr
CHR: fold-simple-expr @ // { Expr ?y { ?w ?xs } } -- [ ?w fold-word? ] [ ?xs ground-value-in-context :>> ?x ground-value? ]
[ ?x <reversed> [ wrapped>> ] map ?w 1quotation with-datastack first :>> ?r drop t ]
|
{ Is ?y ?r }
[ ?xs [ Dead boa ] map ]
    ;


! ** Trigger Inference
! CHR: request-unknown-effect @ Is{ ?b { execute A{ ?w } ?a } } // --
! [ ?w no-compile? not ] [ ?w { if } in? not ] [ ?w "predicating" word-prop not ] |
! { InferWord ?w } ;
! CHR: request-unknown-effect @ Is{ ?b { execute A{ ?w } ?a } } // --
! [ ?w no-compile? not ] [ ?w { ? } in? not ] [ ?w "predicating" word-prop not ] |
! { InferWord ?w } ;


CHR: infer-regular-word @ { InferWord A{ ?w } } // -- [ ?w generic? not ] [ ?w def>> :>> ?q ] |
! NOTE: first putting the effect is another way to prevent circular inference
{ Is ?b { call ?q ?a } }
{ InferEffect ?w f ?a ?b f }
! { Effect ?w f ?a ?b f }
    ;

CHR: infer-callable @ { InferWord A{ ?q } } // -- [ ?q callable? ] |
{ Is ?b { call ?q ?a } }
{ InferEffect ?q f ?a ?b f } ;

CHR: infer-quot-var @ // { InferQuot ?w ?q } -- |
{ InferWord ?w }
{ Is ?b { call ?q ?a } }
{ InferEffect ?w f ?a ?b f } ;

! ** Resolve Recursive Call Sites
CHR: apply-recusive-call-effect @ AS: ?e P{ Effect ?w ?c ?s ?t ?k } // { RecursiveExec ?a ?b ?w } -- |
[| | ?e instantiate-effect
 [ in>> ] [ out>> ] [ constraints>> ] tri :> ( in out body )
 Is{ in ?a }
 Is{ ?b out }
 body 3array ] ;

! ** Wrap up inferred Effect
! CHR: finish-infer-effect @ // { InferWord ?n } { InferEffect ?n ?c ?a ?b ?k } -- |
CHR: finish-infer-effect @ { InferWord ?n } // { InferEffect ?n ?c ?a ?b ?k } -- |
{ Effect ?n ?c ?a ?b ?k } ;

CHR: cleanup-inferred-effect @ { Effect ?n __ ?a ?b __ } // { InferWord ?n } -- [ ?b vars :>> ?v ] |
{ Marked ?v } ;


! ** Cleanup
! Clean up all contexts!
CHR: mark-types @ // { Marked ?v } { C ?c <={ type-pred ?x . ?y } } -- [ ?x vars ?v subset? ] [ ?v ?x vars union ?y vars union :>> ?w ] |
{ Marked ?w } ;
CHR: mark-effects @ // { Marked ?v } { C ?c P{ Effect ?x __ ?a ?b __ } } -- [ ?x ?v in? ] [ ?v ?a vars union ?b vars union :>> ?w ] |
{ Marked ?w } ;

CHR: end-mark @ // { Marked __ } -- | ;
! CHR: mark-once @ { Mark ?k ?x } // { Mark ?k ?x } -- | ;
! CHR: mark-sweep-trans @ { Mark ?k ?s } // { Trans ?s ?t __ } -- | { Mark ?k ?t } ;
! ! CHR: mark-stack @ { Mark ?k ?s } // { Stack ?s ?x } -- | [ ?x vars [ ?k swap Mark boa ] map ] ;
! CHR: mark-stack @ // { Mark ?k ?s } { Stack ?s ?x } -- | ;
! CHR: end-mark @ // { Mark __ __ } -- | ;

! CHR: collect-marks @ // { Marked ?k ?a } { Mark ?k ?x } -- [ ?a ?x suffix :>> ?b drop t ] | { Marked ?k ?b } ;
! ! CHR: sweep-leftover-effects @ { Marked ?w ?a } // AS: ?p P{ Effect ?q __ __ __ __ } --
! ! [ ?q ?w == not ] [ ?q ?a in? ] | ;
! ! CHR: sweep-leftover @ { Marked __ ?a } // AS: ?p <={ type-pred } -- [ ?p free-vars ?a subset? ] | ;
! CHR: end-marked @ // { Marked __ __ } -- | ;

    ;
