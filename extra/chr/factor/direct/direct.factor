USING: accessors arrays assocs chr chr.comparisons chr.factor chr.factor.defs
chr.parser chr.state classes combinators combinators.short-circuit effects
kernel lists math math.parser namespaces quotations sequences sets strings terms
types.util words words.symbol ;

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
TUPLE: BuildQuot < chr-pred quot ;
TUPLE: BuildNamedCall < chr-pred name quot ;
TUPLE: BuildExecRule < chr-pred name quot ;
! TUPLE: DefCallRule < chr-pred name start end ;
TUPLE: DefCallRule < chr-pred name start end body ;
TUPLE: AddRule < chr-pred rule ;
TUPLE: TransRule < chr-pred head body ;
TUPLE: Mark < chr-pred ctx val ;
TUPLE: Marked < chr-pred ctx vals ;
TUPLE: Effect < chr-pred word in out constraints ;
TUPLE: EffectGen < chr-pred word in out body ;
TUPLE: Eval < chr-pred word in out ;
TUPLE: Definition < chr-pred name quot ;

! Val stuff
TUPLE: Sum < chr-pred x y z ;
! TUPLE: Drop < chr-pred val ;
TUPLE: Use < chr-pred val ;

! Conditional Stuff
TUPLE: Rule < chr-pred cond body ;
TUPLE: Mux < chr-pred cond val then else ;
TUPLE: C < chr-pred cond then else ;
! Parametric Maybe type
! TUPLE: Maybe <

TERM-VARS: Q ;

CHRAT: quots { }
IMPORT: chrat-comp
! Extending the solver at runtime
CHR: add-dynamic-rule @ { AddRule ?r } // -- |
[ ?r extend-program f ] ;

! Stack and transition build-up
CHR: stack-match @ { Stack ?s ?a } // { Stack ?s ?b } -- | [ ?a ?b ==! ] ;
CHR: empty-quot @ // { Transeq ?s ?t [ ] } -- | [ ?s ?t ==! ] ;
CHR: destructure-quot @ // { Transeq ?s ?t ?p } -- [ ?p first :>> ?w ?p rest :>> ?q ?s seq-state :>> ?s0 3drop t ] |
{ Trans ?s ?s0 ?w }
{ Transeq ?s0 ?t ?q } ;

! Early replacement
CHR: inline-if @ // { Trans ?s ?t if } -- | { Transeq ?s ?t [ ? call ] } ;

! Effect-based destructuring
CHR: effect-predicate @ { Trans ?s ?t A{ ?w } } // -- [ ?w callable-word? ]
! [ ?w quot-sym? not ]
[ ?w defined-effect :>> ?e ]
[ ?e effect>stacks [ :>> ?a ] [ :>> ?b ] bi* 2drop t ]
|
{ Stack ?s ?a }
{ Stack ?t ?b }
! Calculate used values
{ Eval ?w ?a ?b }
    ;


CHR: infer-callable @ // { Trans ?s ?t ?q } -- [ ?q callable? ] |
{ Trans ?s ?t Q }
{ Stack ?s ?xs }
{ Stack ?t L{ Q . ?xs } }
{ BuildNamedCall Q ?q }
{ Definition Q ?q }
;

CHR: push-effect @ { Trans ?s ?t ?w } // -- [ ?w callable-word? not ] |
{ Stack ?s ?xs }
{ Stack ?t L{ ?w . ?xs } } ;

! Simple Type stuff
CHR: literal-instance @ // { Instance A{ ?v } ?t } -- |
[ ?v ?t instance? not [ { ?v ?t "not instance" } throw ] when f ] ;

! Effect Type stuff

CHR: redundant-effect @ { Effect ?w ?a ?b ?l } // { Effect ?w ?x ?y ?k } -- [ ?k ?l subset? ] | ;

! NOTE: This does generate a new Effect definition.  In any case, Multiple
! Effect constraints should all somehow influence a { call ... } construct.
! Probably should keep those around?  This here should ensure that we reduce
! duplicate application of constraints as much as possible.  Effectively, this
! is akin to higher-order intersection types?
CHR: same-quot-effect @ { Effect ?w ?a ?b ?l } // { Effect ?w ?x ?y ?k } -- |
[| | ?k ?l diff :> new-constraints
 P{ Effect ?w ?x ?y new-constraints } ] ;

! NOTE: this is probably the universal quantifier equivalent of inferred function types?
CHR: apply-call-effect @ { Eval call L{ ?w . ?a } ?b } { Effect ?w ?rho ?sig ?k } // -- [ ?k empty? not ] |
[| | { ?rho ?sig ?k } fresh first3 :> ( rho sig body )
 [ ?a rho ==! ]
 [ ?b sig ==! ] 2array
 body append
] ;

CHR: apply-dip-effect @ // { Eval dip L{ ?w ?x . ?a  } L{ ?x . ?b } } -- |
{ Eval call L{ ?w . ?a } ?b } ;

! ** Here be special per-word stuff

CHR: call-declares-effect @ { Trans ?r ?u call } { Stack ?r L{ ?w . ?a } } { Stack ?u ?b } // -- |
{ Use ?w }
{ Effect ?w ?a ?b f } ;

! CHR: dip-declares-effect @ { Trans ?r ?u dip L{ ?q ?x . ?a } L{ ?x . ?b } } { Stack  }
CHR: dip-declares-effect @ { Eval dip L{ ?q ?x . ?a } L{ ?y . ?b } } // -- |
[ ?x ?y ==! ]
{ Use ?q }
{ Effect ?q ?a ?b f } ;

CHR: plus-is-sum @ // { Eval + L{ ?x ?y . __ } L{ ?z . __ } } -- |
{ Instance ?x number }
{ Instance ?y number }
{ Instance ?z number }
{ Sum ?x ?y ?z } ;

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
CHR: dup-effect-1 @ { Dup ?p ?q } { Effect ?p ?a ?b ?l } // -- | { Effect ?q ?a ?b ?l } ;
CHR: dup-effect-2 @ { Dup ?q ?p } { Effect ?p ?a ?b ?l } // -- | { Effect ?q ?a ?b ?l } ;
CHR: unique-instance @ { Instance ?x ?tau } // { Instance ?x ?tau } -- | ;
CHR: dup-instance-1 @ { Dup ?x ?y } { Instance ?x ?tau } // -- | { Instance ?y ?tau } ;
CHR: dup-instance-2 @ { Dup ?y ?x } { Instance ?x ?tau } // -- | { Instance ?y ?tau } ;

! CHR: effect-use @ { Use ?q } // { Effect ?q __ __ __ } -- | ;
CHR: uninteresting-use @ // { Use A{ ?x } } -- | ;
! CHR: definition-use @ // { Definition ?p _ } ;

! Uses cancel dups
CHR: dead-dup-1 @ // { Dup ?x ?y } { Use ?y } -- | [ ?x ?y ==! ] ;
CHR: dead-dup-2 @ // { Dup ?x ?y } { Use ?x } -- | [ ?x ?y ==! ] ;


! Lift the choice into the value!  Is that a boolean type constructor???
! NOTE: not doing that on the stack to simplify value handling
CHR: do-mux @ // { Eval ? L{ ?q ?p ?c . __ } L{ ?v . __ } } -- |
! [ ?v P{ C ?c ?p ?q } ==! ] ;
{ Mux ?c ?v ?p ?q } ;

! Predicate words
CHR: add-predicate-rules @ { Eval ?w L{ ?v . __ } L{ ?c . __ } } // -- [ ?w "predicating" word-prop :>> ?tau ] [ P{ Instance ?v ?tau } :>> ?p ] |
{ C ?c ?p P{ Not ?p } }
{ Use ?v }
    ;
! P{ C ?c P{ Instance ?v ?tau } P{ Not P{ Instance ?v ?tau } } }
! { Instance ?v P{ C ?c ?tau Not{  } }}

! ** Subordinate inference
CHR: build-quot-body @ // { BuildQuot ?q } -- |
{ Transeq +top+ +end+ ?q } ;

! For call rules
CHR: build-named-call-def @ // { BuildNamedCall ?n ?q } -- |
{ Transeq ?s ?t ?q }
{ Mark ?n ?s }
! { Mark ?n ?t }
{ Marked ?n f }
{ DefCallRule ?n ?s ?t f } ;

! For regular word rules
CHR: build-word-exec-rule @ // { BuildExecRule ?w ?q } -- |
{ Transeq ?s ?t ?q }
{ Mark ?w ?s }
{ Marked ?w f }
{ DefCallRule ?w ?s ?t f } ;

! Collect inlined quots
! CHR: quot-use @ // { Use ?q } { Effect ?q __ __ __ } { Definition ?q __ } -- | ;

! Collect predicates
CHR: mark-once @ { Mark ?k ?x } // { Mark ?k ?x } -- | ;
CHR: mark-trans @ { Mark ?k ?s } { Trans ?s ?t __ } // -- | { Mark ?k ?t } ;
CHR: mark-stack @ { Mark ?k ?s } { Stack ?s ?x } // -- | [ ?x vars [ ?k swap Mark boa ] map ] ;
CHR: collect-marks @ // { Marked ?k ?a } { Mark ?k ?x } -- [ ?a ?x suffix :>> ?b drop t ] | { Marked ?k ?b } ;

DEFER: make-simp-rule

! TODO Don't call for callable values?
! Create rule for quotations
CHR: build-call-rule @ // { DefCallRule ?n ?s ?t f } { Marked ?n ?l } { Stack ?s ?a } { Stack ?t ?b } -- |
[| | store get values rest
 [ vars>> [ ?l in? ] all? ] filter
 :> body-chrs
 body-chrs [ id>> kill-chr ] each
 body-chrs [ constraint>> ] map
 [ Trans? ] reject
 ! NOTE: this one here may be worth keeping if it is needed for call graph analysis?
 ! Although, the Effect predicate pretty much expresses the same stuff...
 [ Eval? ] reject
 [ Stack? ] reject
 ! TODO: possibly leave them in there for inline words?  Really they are constant value definitions though...
 [ Definition? ] reject
 ! [ { [ Stack? ] [ s1>> { [ ?s == ] [ ?t == ] } 1|| not ] } 1&& ] reject
 :> word-constraints
 P{ Effect ?n ?a ?b word-constraints }
] ;

;

! * External

: build-quot ( thunk -- chrs )
    quots swap BuildQuot boa 1array run-chr-query values rest ;

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
    [ def>> ] keep swap BuildExecRule boa 1array quots swap run-chr-query values rest ;
