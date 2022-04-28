USING: accessors arrays assocs chr chr.comparisons chr.factor chr.factor.defs
chr.parser chr.state classes classes.algebra combinators
chr.factor.terms
combinators.short-circuit effects generic.math kernel kernel.private lists match
math math.parser namespaces quotations sequences sets strings terms types.util
words words.symbol ;

IN: chr.factor.direct

PREDICATE: quot-sym < word "quot-id" word-prop? ;
: <quot-sym> ( name -- word ) usym dup t "quot-id" set-word-prop ;

PREDICATE: callable-word < word { [ symbol? not ] [ quot-sym? not ] } 1&& ;
! PREDICATE: callable-word < word symbol? not ;

: pluck ( seq quot: ( elt -- ? ) -- seq' elt )
    dupd find [ remove-nth ] keep ; inline

: stack-match ( stack-var elts rest -- chr )
    [ __ ] unless*
    [ >list ] dip list*
    <eq-constraint> ;

GENERIC: elt>var ( i elt -- obj )
M: f elt>var drop number>string "v" prepend utermvar ;
M: string elt>var nip utermvar ;
M: pair elt>var
    first2 drop elt>var ;

: elt-vars ( seq -- seq )
    [ swap elt>var ] map-index <reversed> ;
    ! [ swap dup pair? [ first ] when
    !   [ nip ] [ number>string "v" prepend ] if*
    !   uvar
    !   <term-var>
    ! ] map-index <reversed> ;

: effect>stack-elts ( effect -- lin lout )
    [ in>> elt-vars >list ]
    [ out>> elt-vars >list ] bi ;

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

: effect>stacks ( effect -- lin lout )
    [ effect>stack-elts ]
    [ add-row-vars ] bi ;

TUPLE: Transeq < chr-pred from to quot ;
TUPLE: Trans < chr-pred from to command ;
TUPLE: BuildQuot < chr-pred from to quot ;
TUPLE: BuildNamedCall < chr-pred name quot ;
! TUPLE: DefCallRule < chr-pred name start end ;
TUPLE: DefCallRule < chr-pred name start end body ;
TUPLE: AddRule < chr-pred rule ;
TUPLE: TransRule < chr-pred head body ;
TUPLE: Mark < chr-pred ctx val ;
TUPLE: Marked < chr-pred ctx vals ;

! Callable Stuff
TUPLE: Call < chr-pred quot in out ;
TUPLE: Effect < chr-pred word parms in out constraints ;
TUPLE: EffectGen < chr-pred word in out body ;
TUPLE: Eval < chr-pred word in out ;
TUPLE: Definition < chr-pred name quot ;

! Val stuff
TUPLE: Sum < chr-pred x y z ;
! TUPLE: Drop < chr-pred val ;
TUPLE: Use < chr-pred val ;
! Cleanup
TUPLE: Used < chr-pred val ;

! Conditional Stuff
TUPLE: Rule < chr-pred cond body ;
TUPLE: Mux < chr-pred cond val then else ;
TUPLE: C < chr-pred cond then ;

TUPLE: --> < chr-pred cond consequence ;
TUPLE: \--> < chr-pred cond consequence ;

! Type Stuff
TUPLE: Provide < chr-pred val type ;
TUPLE: Require < chr-pred val type ;

! Var stuff
GENERIC: bound-vars ( pred -- vars )
M: chr-pred bound-vars drop f ;
GENERIC: free-vars ( pred -- vars )
M: chr-pred free-vars
    constraint-args free-vars ;
M: sequence free-vars [ free-vars ] gather ;
M: term-var free-vars 1array ;
M: object free-vars drop f ;
M: Effect bound-vars [ parms>> ] [ in>> vars union ] [ out>> vars union ] tri ;
M: Effect free-vars [ constraints>> free-vars ] [ bound-vars diff ] bi ;

TERM-VARS: Q ;

CHRAT: quots { }
IMPORT: chrat-comp
! Set semantics
CHR: unique-requires @ { Require ?x ?tau } // { Require ?x ?tau } -- | ;
CHR: require-intersection @ // { Require ?x A{ ?tau } } { Require ?x A{ ?sig } } -- [ ?tau ?sig class-and :>> ?s ] | { Require ?x ?s } ;
! CHR: require-same-type @ { Require ?x ?tau } // { Require ?x ?sig } -- [ ?sig term-var? ] | [ ?sig ?tau ==! ] ;

CHR: unique-provides @ { Provide ?x ?tau } // { Provide ?x ?tau } -- | ;
CHR: provide-intersection @ { Provide ?x A{ ?tau } } // { Provide ?x A{ ?sig } } -- [ ?tau ?sig class-and :>> ?s ] | { Provide ?x ?s } ;
! CHR: provide-same-type @ { Provide ?x ?tau } // { Provide ?x ?sig } -- [ ?sig term-var? ] | [ ?sig ?tau ==! ] ;

CHR: unique-use @ { Use ?x } // { Use ?x } -- | ;

! Cleanup
CHR: used-use-literal @ // { Use A{ ?x } } -- | ;
CHR: used-used-literal @ // { Used A{ ?x } } -- | ;
CHR: check-literal-require @ // { Require A{ ?x } A{ ?tau } } -- |
[ ?x ?tau instance? [ "nope" throw ] unless f ] ;
CHR: check-literal-provide @ // { Provide A{ ?x } A{ ?tau } } -- |
[ ?x ?tau instance? [ "nopenope" throw ] unless f ] ;
! CHR: used-effect @ { Used ?q } // { Effect ?q __ __ __ __ } -- | ;

! Extending the solver at runtime
CHR: add-dynamic-rule @ { AddRule ?r } // -- |
[ ?r extend-program f ] ;
SYMBOL: nop
! Stack and transition build-up
CHR: stack-match @ { Stack ?s ?a } // { Stack ?s ?b } -- | [ ?a ?b ==! ] ;
! CHR: empty-quot @ // { Transeq ?s ?t A{ [ ] } } -- | { Stack ?s ?rho } { Stack ?t ?rho } ;
! CHR: empty-quot @ // { Transeq ?s ?t A{ [ ] } } -- | { Stack ?s ?rho } { Stack ?t ?rho } ;
CHR: empty-quot @ // { Transeq ?s ?t [ ] } -- | [ ?s ?t ==! ] ;
CHR: destructure-quot @ // { Transeq ?s ?t ?p } -- [ ?p first dup callable-word? [ <wrapper> ] unless :>> ?w ?p rest :>> ?q ?s seq-state :>> ?s0 3drop t ] |
{ Trans ?s ?s0 ?w }
{ Transeq ?s0 ?t ?q } ;

! Early replacement
CHR: inline-if @ // { Trans ?s ?t if } -- | { Transeq ?s ?t [ ? call ] } ;

! Effect-based destructuring
CHR: effect-predicate @ { Trans ?s ?t A{ ?w } } // -- [ ?w callable-word? ]
! [ ?w quot-sym? not ]
[ ?w defined-effect :>> ?e ]
[ ?e effect>stacks [ :>> ?a ] [ :>> ?b ] bi* 2drop t ]
! [ ?a list>array* :>> ?i ]
! [ ?b list>array* :>> ?o ]
|
{ Stack ?s ?a }
{ Stack ?t ?b }
{ Eval ?w ?a ?b }
    ;


! CHR: remove-used-quot-trans @ { Used ?q } // { Trans ?s ?t ?q } -- | ;

! CHR: infer-callable @ // { Trans ?s ?t A{ ?q } } -- [ ?q callable? ] |
CHR: infer-callable @ // { Trans ?s ?t ?q } -- [ ?q callable? ] |
{ Trans ?s ?t Q }
{ Stack ?s ?xs }
{ Stack ?t L{ Q . ?xs } }
{ BuildNamedCall Q ?q }
{ Definition Q ?q }
;

CHR: push-effect @ { Trans ?s ?t A{ ?w } } // -- ! [ break ?v wrapper? ] [ ?v wrapped>> :>> ?w drop t ]
[ ?w callable-word? not ] [ ?w :>> ?v drop t ] [ ?w class-of :>> ?tau ] |
{ Stack ?s ?xs }
{ Definition ?x ?v }
{ Stack ?t L{ ?x . ?xs } }
{ Provide ?x ?tau }
;

! Simple Type stuff
CHR: literal-instance @ // { Instance A{ ?v } ?t } -- |
[ ?v ?t instance? not [ { ?v ?t "not instance" } throw ] when f ] ;

! ** Effect Type stuff

CHR: redundant-effect @ { Effect ?w ?c ?a ?b ?l } // { Effect ?w ?d ?x ?y ?k } -- [ ?d ?c subset? ] [ ?k ?l subset? ] | ;
! TODO: maybe do, because of effect matching?
! [ { ?a ?x } { ?b ?y } ==! ] ;

! NOTE: This does generate a new Effect definition.  In any case, Multiple
! Effect constraints should all somehow influence a { call ... } construct.
! Probably should keep those around?  This here should ensure that we reduce
! duplicate application of constraints as much as possible.  Effectively, this
! is akin to higher-order intersection types?
! CHR: same-quot-effect @ { Effect ?w ?c ?a ?b ?l } // { Effect ?w ?c ?x ?y ?k } -- [ ?k ?l intersects? ] |
! [| | ?k ?l diff :> new-constraints
!  P{ Effect ?w ?c ?x ?y new-constraints } ] ;

: instantiate-effect ( effect -- in out body )
    { [ in>> ] [ out>> ] [ constraints>> 3array dup term-vars ] [ parms>> diff ] } cleave
    fresh-with first3 ;

! ** Expand Effect Conjunctions
! The idea here is: whenever there are conflicting definitions about effects:
! Create a new one, throw all predicates into the store, and collect the ones with the corresponding binder
CHR: rebuild-effect-conjunction @ // AS: ?r P{ Effect ?p ?c ?a ?b ?k } AS: ?s P{ Effect ?p ?d ?x ?y ?l } -- |
[| |
 ?r instantiate-effect :> ( a b k )
 ?s instantiate-effect :> ( x y l )
 ! [ { ?a ?b } { ?x ?y } ==! ] 1array
 k l append
 [ { a b } { x y } ==! ] suffix
 ! [ { ?rho ?sig } { a b } ==! ] suffix
 ?c ?d union :> parms
 P{ Effect ?p parms a b f } suffix
] ;


! ** Conditional reasoning
CHR: duplicate-constraints @ { C ?c ?x } // { C ?c ?x } -- | ;
CHR: expand-conjunction @ // { C ?p ?b } -- [ ?b sequence? ] |
[| |
?b [ ?p swap C boa ] map
] ;
CHR: lift-tautologies @ // { C ?c ?x } { C P{ Not ?c } ?x } -- |
[ ?x ] ;

! Distribute Conditional statements
! CHR: mux-prop-use @ { Mux __ ?v ?x ?y } { Use ?v } // -- | { Use ?x } { Use ?y } ;
! CHR: both-vals-used @ { Mux __ ?v ?x ?y } { Used ?x } { Used ?y } // -- | { Used ?v } ;
! CHR: mux-prop-require @ { Mux ?c ?v ?x ?y } { Require ?v ?tau } // -- | { C ?c P{ Require ?x ?tau } } { C P{ Not ?c } P{ Require ?y ?tau } } ;
! CHR: mux-prop-effect @ { Mux ?c ?q ?x ?y } { Effect ?v ?d ?a ?b ?k } // -- [ ?c ?d in? not ] [ P{ Not ?c } ?d in? not ] [ ?d ?c suffix :>> ?e ] [ ?d P{ Not ?c } suffix :>> ?l ] |
! { Effect ?x ?e ?a ?b ?k }
! { Effect ?y ?l ?a ?b ?k } ;
 ! { C ?c P{ Effect ?x ?d ?a ?b ?k } }
 ! { C P{ Not ?c } P{ Effect ?y ?d ?a ?b ?k } } ;

! CHR: distribute-effect-condition @ // { C ?c P{ Effect ?q ?d ?a ?b ?k } } -- [ ?d ?c suffix members :>> ?e ] |
! { Effect ?q ?e ?a ?b ?k } ;


! Builtin Types
! Lifting from branches
! CHR: least-possible-lit-type @ { C ?c P{ Provide ?x A{ ?tau } } } { C P{ Not ?c } P{ Provide ?x A{ ?sig } } } //
! -- [ ?tau ?sig class-and dup null = [ drop f ] when :>> ?y ] ! [ ?tau ?sig ?y class= class= and not ]
! |
! { Provide ?x ?y } ;
CHR: provide-conjunction @ { C ?c P{ Provide ?x A{ ?tau } } } { C P{ Not ?c } P{ Provide ?x A{ ?sig } } } // -- [ ?tau ?sig class-or :>> ?s ]
| { Provide ?x ?s } ;

CHR: require-conjunction @ { C ?c P{ Require ?x A{ ?tau } } } { C P{ Not ?c } P{ Require ?x A{ ?sig } } } // -- [ ?tau ?sig class-and :>> ?s ]
| { Require ?x ?s } ;


! ** Mux effects

! If we know something about the mux inputs
CHR: mux-effect-1 @ { Mux ?c ?v ?p __ } { Effect ?p ?d ?r ?s ?x } // -- [ ?c ?d in? not ] [ ?d ?c suffix :>> ?e ] |
{ Effect ?v ?e ?r ?s { P{ C ?c ?x  } } } ;
CHR: mux-effect-2 @ { Mux ?c ?v __ ?q } { Effect ?q ?d ?r ?s ?x } // -- [ ?c ?d in? not ] [ ?d ?c suffix :>> ?e ] |
{ Effect ?v ?e ?r ?s { P{ C P{ Not ?c } ?x } } } ;

! ** Constract Effects


! This is the collector
CHR: bind-provides @ AS: ?k P{ Provide __ __ } // AS: ?e P{ Effect __ __ __ __ ?l } --
[ ?k ?l in? not ]
[ ?k free-vars ?e bound-vars subset? ] |
[ ?e clone [ ?k suffix ] change-constraints ] ;

! | [  ] ;
! CHR: bind-effect @ AS: ?k P{ Effect ?q __ __ __ __  } // AS: ?e P{ Effect __ __ __ __ __ } -- |
! [ ?q ?c ?a ?b [ vars ] tri@ union ]

! ** Apply Effects at call sites

! NOTE: this is probably the universal quantifier equivalent of inferred function types?
! CHR: apply-call-effect @ { Eval call L{ ?w . ?a } ?b } // { Effect ?w ?c ?rho ?sig ?k } -- |
CHR: apply-call-effect @ { Call ?w ?a ?b } AS: ?e P{ Effect ?w ?c ?rho ?sig ?k } // -- |
[| | ?e instantiate-effect :> ( rho sig body )
 body
 [ ?a rho ==! ]
 [ ?b sig ==! ] 2array append
 ! body ?c [ [ swap C boa ] with map ] when* append
] ;

! Use-case: known effects are muxed, merged effect is calculated
! CHR: mux-effect @ { Mux ?c ?v ?p ?q } { Effect ?p ?d ?r ?s ?x } { Effect ?q ?e ?t ?u ?y } // --
! [ ?c ?d in? not ] [ ?e ?c suffix :>> ?n ] |
! { Effect ?v ?n ?r ?s { P{ C ?c ?x } } }
! { Effect ?v ?n ?t ?u { P{ C P{ Not ?c } ?y } } } ;
! [| |
!  C{  }
!  ?d ?c prefix :> c1
!  ?e P{ Not ?c } prefix :> c2
!  f
! { Effect ?v c1 ?r ?s ?x } suffix
! { Effect ?v c2 ?t ?u ?y } suffix ] ;

! Use-case: unknown effect, but it is known to be muxed, so the condition must apply
! CHR: cond-effect-1 @ { Mux ?c ?v ?p ?q } { Effect ?p ?d ?r ?s ?x } // -- [ ?c ?d in? not ] [ ?d ?c suffix :>> ?e ] |
! { Effect ?p ?e ?r ?s ?x } ;

! CHR: cond-effect-2 @ { Mux ?c ?v ?p ?q } { Effect ?q ?d ?r ?s ?x } // -- [ P{ Not ?c } ?d in? not ] [ ?d P{ Not ?c } suffix :>> ?e ] |
! { Effect ?p ?e ?r ?s ?x } ;

! Use-case: muxed effect, branches unknown, but effect must be compatible
! TODO: do we need to pull in the bodies and conditions as well?
! CHR: muxed-effect-shapes @ { Mux __ ?v ?p ?q } { Effect ?v __ ?r ?s __ } // -- | { Effect ?p f ?r ?s f } { Effect ?q f ?r ?s f } ;


CHR: apply-dip-effect @ // { Eval dip L{ ?w ?x . ?a  } L{ ?x . ?b } } -- |
{ Eval call L{ ?w . ?a } ?b } ;

! ** Here be special per-word stuff

! TODO: check if it is necessary to do this on trans?
CHR: call-declares-effect @ { Trans ?r ?u call } { Stack ?r L{ ?w . ?a } } { Stack ?u ?b } // -- |
{ Effect ?w f ?a ?b f } ;

CHR: do-call @ // { Eval call L{ ?q . ?a } ?b } -- | { Call ?q ?a ?b } { Use ?q } ;

CHR: dip-declares-effect @ { Eval dip L{ ?q ?x . ?a } L{ ?y . ?b } } // -- |
[ ?x ?y ==! ]
{ Effect ?q f ?a ?b f } ;

CHR: math-uses-numbers @ { Eval ?w L{ ?x ?y . __ } __ } // -- [ ?w math-generic? ] |
{ Require ?x number }
{ Require ?y number }
{ Use ?x }
{ Use ?y } ;

CHR: plus-is-sum @ // { Eval + L{ ?x ?y . __ } L{ ?z . __ } } -- |
{ Provide ?z number }
{ Sum ?x ?y ?z } ;

! CHR: curry-effect @ { Eval curry L{ ?q ?x . ?a } __ } // -- |
! CHR: curry-effect @ { Eval curry L{ ?p ?x . __ } L{ ?q . __ } } { Effect ?p ?c ?rho ?sig ?k } // -- |
! [ L{ ?y . ?a } ?rho ==! ]
! [| | P{ is ?y ?x }
! { Effect ?q ?c ?a ?sig ?k } ] ;

! Basic data flow

: effect-dups ( effect -- assoc )
    [ in>> ] [ out>> ] bi
    [| elt index out | index elt out indices ?rest 2array ] curry map-index ;

CHR: do-shuffle @ // { Eval ?w ?a ?b } -- [ ?w "shuffle" word-prop :>> ?e ] |
[| |
 ?a list>array* <reversed> :> in
 in ?e shuffle :> out
 f
 ?e effect-dups [| i inds |
                 i in nth :> in-var
                 inds [
                     [| oi |
                      in-var name>> utermvar :> dupvar
                      dupvar oi out set-nth
                      in-var dupvar Dup boa suffix
                     ] each
                 ] [ in-var Use boa suffix ] if*
                ] assoc-each
 out <reversed> >list __ list* :> b-pat
 [ ?b b-pat ==! ] suffix
] ;

CHR: self-dup @ // { Dup ?x ?x } -- | ;
! Be eager in duplicating quot-representing values, because their effect defs
! are instantiated with fresh vars if called.  Actually extend this to all non-vars!
CHR: unique-def @ { Definition ?p ?q } // { Definition ?p ?q } -- | ;
CHR: dup-definition-1 @ { Dup ?p ?q } { Definition ?p ?v } // -- | { Definition ?q ?v } ;
CHR: dup-definition-2 @ { Dup ?q ?p } { Definition ?p ?v } // -- | { Definition ?q ?v } ;
CHR: dup-effect-1 @ { Dup ?p ?q } { Effect ?p ?c ?a ?b ?l } // -- | { Effect ?q ?c ?a ?b ?l } ;
CHR: dup-effect-2 @ { Dup ?q ?p } { Effect ?p ?c ?a ?b ?l } // -- | { Effect ?q ?c ?a ?b ?l } ;
CHR: unique-instance @ { Instance ?x ?tau } // { Instance ?x ?tau } -- | ;
CHR: dup-instance-1 @ { Dup ?x ?y } { Instance ?x ?tau } // -- | { Instance ?y ?tau } ;
CHR: dup-instance-2 @ { Dup ?y ?x } { Instance ?x ?tau } // -- | { Instance ?y ?tau } ;

! Uses cancel dups
CHR: dead-dup-1 @ // { Dup ?x ?y } { Use ?y } -- | [ ?x ?y ==! ] ;
CHR: dead-dup-2 @ // { Dup ?x ?y } { Use ?x } -- | [ ?x ?y ==! ] ;

! Lift the choice into the value!  Is that a boolean type constructor???
! NOTE: not doing that on the stack to simplify value handling
CHR: do-mux @ // { Eval ? L{ ?q ?p ?c . __ } L{ ?v . __ } } -- |
! [ ?v P{ C ?c ?p ?q } ==! ] ;
{ Mux ?c ?v ?p ?q }
{ Use ?c } ;

! Predicate words
CHR: add-predicate-rules @ { Eval ?w L{ ?v . __ } L{ ?c . __ } } // --
[ ?w "predicating" word-prop :>> ?tau ] |
! { C ?c P{ Require ?v ?tau } }
{ C ?c P{ Provide ?v ?tau } }
{ Provide ?c boolean }
{ Use ?v }
    ;

! Declarations
! NOTE: Only doing provide here, which is in effect a down-cast
CHR: do-declare @ { Definition ?x A{ ?tau } } // { Eval declare L{ ?x . ?a } ?b } -- |
[| |
 ?tau length [ "v" utermvar ] replicate :> vars
 vars >list ?rho list* :> var-stack
 [ ?b var-stack ==! ]
 [ ?a var-stack ==! ] 2array
 vars ?tau [ Provide boa ] 2map append
 { Use ?x }
] ;

! ** Subordinate inference
CHR: build-quot-body @ // { BuildQuot ?s ?t ?q } -- |
[ ?q empty? [ { Stack ?s ?rho  } { Stack ?t ?rho } 2array ]
  [ { Transeq ?s ?t ?q } ] if
] ;
! { Transeq +top+ +end+ ?q } ;

! For call rules
CHR: build-named-call-def @ // { BuildNamedCall ?n A{ ?p } } -- [ ?p :>> ?q ] |
{ BuildQuot ?s ?t ?q }
{ DefCallRule ?n ?s ?t f }
{ Mark ?n ?s }
{ Mark ?n ?t }
{ Marked ?n f } ;

! Collect predicates
CHR: mark-once @ { Mark ?k ?x } // { Mark ?k ?x } -- | ;
CHR: mark-trans @ { Mark ?k ?s } { Trans ?s ?t __ } // -- | { Mark ?k ?t } ;
CHR: mark-stack @ { Mark ?k ?s } { Stack ?s ?x } // -- | [ ?x vars [ ?k swap Mark boa ] map ] ;
CHR: collect-nested-effect @ { Mark ?k ?q } // { Effect ?q ?c ?a ?b ?l } { DefCallRule ?k ?s ?t ?x } -- [ ?x P{ Effect ?q ?c ?a ?b ?l } suffix :>> ?y ] |
{ DefCallRule ?k ?s ?t ?y } ;

CHR: collect-marks @ // { Marked ?k ?a } { Mark ?k ?x } -- [ ?a ?x suffix :>> ?b drop t ] | { Marked ?k ?b } ;

DEFER: make-simp-rule

: group-conditionals ( body -- body )
    [ C? ] partition swap
    [ cond>> ] collect-by
    [ [ then>> ] map >array C boa suffix ] assoc-each
    ;

! TODO Don't call for callable values?
! Create rule for quotations
CHR: build-call-rule @ // { DefCallRule ?n ?s ?t ?x } { Marked ?n ?l } { Stack ?s ?a } { Stack ?t ?b } -- |
[| | store get values rest
 [ vars>> [ ?l in? ] all? ] filter
 :> body-chrs
 body-chrs [ id>> kill-chr ] each
 body-chrs [ constraint>> ] map
 ?x append
 [ Trans? ] reject
 ! NOTE: this one here may be worth keeping if it is needed for call graph analysis?
 ! Although, the Effect predicate pretty much expresses the same stuff...
 [ Eval? ] reject
 [ Stack? ] reject
 [ Used? ] reject
 ! TODO: possibly leave them in there for inline words?  Really they are constant value definitions though...
 [ Definition? ] reject
 [ Call? ] reject
 ! XXX: is this true? In a sense it should be, it just has to be made sure that the effect includes those!
 [ C? ] reject
 ! [ { [ Stack? ] [ s1>> { [ ?s == ] [ ?t == ] } 1|| not ] } 1&& ] reject
 group-conditionals
 :> word-constraints
 P{ Effect ?n f ?a ?b word-constraints }
] ;

! Cleanup used vals

CHR: used-definition-is-lit @ { Definition ?x A{ ?v } } // { Use ?x } -- |
[ ?v callable? not [ ?x ?v ==! ] [ f ] if ]
{ Used ?x }
    ;

;

! * External

: build-quot ( thunk -- chrs )
    quots swap [ +top+ +end+ ] dip BuildQuot boa 1array run-chr-query values rest ;

: build-word ( word -- chrs )
    def>> build-quot ;

: build-quot-rule ( thunk name -- chrs )
    swap BuildNamedCall boa 1array quots swap run-chr-query values rest ;

:: make-simp-rule ( heads body word -- rule )
    word name>> :> wname
    wname "-call" append :> rname
    heads 0 f body f named-chr new-chr rname >>rule-name ;

GENERIC: build-type ( word -- chrs )
M: callable build-type
    "anon" usym build-quot-rule ;
M: word build-type
    [ def>> ] keep swap BuildNamedCall boa 1array quots swap run-chr-query values rest ;
