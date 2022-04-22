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

TUPLE: Q < chr-pred name ;

GENERIC: elt>var ( i elt -- obj )
M: f elt>var drop number>string "v" prepend utermvar ;
M: string elt>var nip utermvar ;
M: pair elt>var
    first2
    [ elt>var ] dip
    effect? [ Q boa ] when ;

: elt-vars ( seq -- seq )
    [ swap elt>var ] map-index <reversed> ;
    ! [ swap dup pair? [ first ] when
    !   [ nip ] [ number>string "v" prepend ] if*
    !   uvar
    !   <term-var>
    ! ] map-index <reversed> ;

! : effect>stacks ( effect -- lin lout )
!     [ in>> elt-vars >list ]
!     [ out>> elt-vars >list ] bi ;

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

! Val stuff
TUPLE: Sum < chr-pred x y z ;
TUPLE: Drop < chr-pred val ;

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

! Effect-based destructuring
CHR: effect-predicate @ { Trans ?s ?t ?w } // -- [ ?w callable-word? ]
! [ ?w quot-sym? not ]
[ ?w defined-effect :>> ?e ]
[ ?e effect>stacks [ :>> ?a ] [ :>> ?b ] bi* 2drop t ]
|
{ Stack ?s ?a }
{ Stack ?t ?b }
{ Eval ?w ?a ?b } ;
! [| | { ?a ?b } ?w prefix ] ;

CHR: infer-callable @ // { Trans ?s ?t ?q } -- [ ?q callable? ] [ "q" <quot-sym> :>> ?p ] |
{ Trans ?s ?t P{ Q ?p } }
{ Stack ?s ?xs }
{ Stack ?t L{ P{ Q ?p } . ?xs } }
{ BuildNamedCall ?p ?q }
;

CHR: push-effect @ { Trans ?s ?t ?w } // -- [ ?w callable-word? not ] [ ?w Q? not ] |
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
! [ ?x ?a ==! ]
! [ ?y ?b ==! ]
[| | ?k ?l diff :> new-constraints
 P{ Effect ?w ?x ?y new-constraints } ] ;

! Temporary? Effect application semantics
! CHR: effect-generator @ { Effect ?w ?a ?b ?l } // -- [ ?l empty? not ] |
! [| |
!  ?a vars ?b vars union ?l vars union :> body-vars
!  P{ is ?sig ?a }
!  P{ is ?rho ?b } 2array
! ?l append body-vars swap <generator>
!  :> generator-body
!  { EffectGen ?w ?sig ?rho generator-body }
! ] ;

! CHR: apply-call-effect @ { call L{ P{ Q ?w } . ?a } ?b } { EffectGen ?w ?rho ?sig ?k } // -- |
! [ ?k H{ { ?sig ?b } { ?rho ?a } } lift ] ;

! NOTE: this is probably the universal quantifier equivalent of inferred function types?
CHR: apply-call-effect @ { Eval call L{ P{ Q ?w } . ?a } ?b } { Effect ?w ?rho ?sig ?k } // -- [ ?k empty? not ] |
[| | { ?rho ?sig ?k } fresh first3 :> ( rho sig body )
 [ ?a rho ==! ]
 [ ?b sig ==! ] 2array
 body append
] ;

! Here be special per-word stuff

CHR: call-declares-effect @ { Trans ?r ?u call } { Stack ?r L{ P{ Q ?w } . ?a } } { Stack ?u ?b } // -- |
{ Effect ?w ?a ?b f } ;

CHR: plus-is-sum @ // { Eval + L{ ?x ?y . __ } L{ ?z . __ } } -- |
{ Instance ?x number }
{ Instance ?y number }
{ Instance ?z number }
{ Sum ?x ?y ?z } ;

! Basic data flow

CHR: dup-defines-split @ // { Eval dup L{ ?x . __ } L{ ?a ?b . __ } } -- |
{ Dup ?x ?a }
{ Dup ?x ?b } ;

CHR: self-dup @ // { Dup ?x ?x } -- | ;
! Be eager in duplicating quot-representing values, because their effect defs
! are instantiated with fresh vars if called.  Actually extend this to all non-vars!
CHR: lit-dup-is-unique @ // { Dup A{ ?v } ?x } -- | [ ?x ?v ==! ] ;
CHR: lit-dupped-is-unique @ // { Dup ?x A{ ?v } } -- | [ ?x ?v ==! ] ;

CHR: do-drop @ // { Eval drop L{ ?x . __ } __ } -- | { Drop ?x } ;

CHR: uninteresting-drop @ // { Drop A{ ?x } } -- | ;

! drops cancel dups
CHR: dead-dup-1 @ // { Dup ?x ?y } { Dup ?x ?z } { Drop ?y } -- | [ ?x ?z ==! ] ;
CHR: dead-dup-2 @ // { Dup ?x ?y } { Dup ?x ?z } { Drop ?z } -- | [ ?x ?y ==! ] ;

CHR: do-swap @ // { Eval swap L{ ?x ?y . __ } L{ ?a ?b . __ } } -- | [ ?x ?b ==! ] [ ?y ?a ==! ] ;

! CHR: curry-defines-callable @



! Subordinate inference
CHR: build-quot-body @ // { BuildQuot ?q } -- |
{ Transeq +top+ +end+ ?q } ;

! For call rules
CHR: build-named-call-def @ // { BuildNamedCall ?n ?q } -- [ ?n Q boa :>> ?w ] |
{ Transeq ?s ?t ?q }
{ Mark ?w ?s }
! { Mark ?n ?t }
{ Marked ?w f }
{ DefCallRule ?w ?s ?t f } ;

! For regular word rules
CHR: build-word-exec-rule @ // { BuildExecRule ?w ?q } -- |
{ Transeq ?s ?t ?q }
{ Mark ?w ?s }
{ Marked ?w f }
{ DefCallRule ?w ?s ?t f } ;

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
 ! [ constraint-type \ call = ] reject
 [ Eval? ] reject
 [ Stack? ] reject
 ! [ { [ Stack? ] [ s1>> { [ ?s == ] [ ?t == ] } 1|| not ] } 1&& ] reject
 dup :> word-constraints
 P{ is ?sig ?b } prefix
 P{ is ?rho ?a } prefix
 :> body
 ?n Q? ?n over [ name>> ] when :> w
 [
     { { call L{ ?n . ?rho } ?sig } }
     body
     ?n name>> make-simp-rule
 ] [ { { ?n ?rho ?sig } } body ?n make-simp-rule ] if
 ! AddRule boa
 drop f
 P{ Effect w ?a ?b word-constraints } 2array
] ;

;

! * External

: build-quot ( quot -- chrs )
    quots swap BuildQuot boa 1array run-chr-query values rest ;

: build-quot-rule ( quot name -- chrs )
    swap BuildNamedCall boa 1array quots swap run-chr-query values rest ;

:: make-simp-rule ( heads body word -- rule )
    word name>> :> wname
    wname "-call" append :> rname
    heads 0 f body f named-chr new-chr rname >>rule-name ;

GENERIC: build-word ( word -- chrs )
M: callable build-word
    "anon" usym build-quot-rule ;
M: word build-word
    [ def>> ] keep swap BuildExecRule boa 1array quots swap run-chr-query values rest ;
