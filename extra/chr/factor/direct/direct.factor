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

! Val stuff
TUPLE: Sum < chr-pred x y z ;

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
[| | { ?a ?b } ?w prefix ] ;

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

! Here be special word stuff
CHR: do-call @ { call L{ ?q . ?a } ?b } // -- |
{ Stack ?r ?a } { Stack ?u ?b }
[| | ?q :> qid
 { Trans ?r ?u qid }
] ;

CHR: plus-is-sum @ // { + L{ ?x ?y . __ } L{ ?z . __ } } -- |
{ Instance ?x number }
{ Instance ?y number }
{ Instance ?z number }
{ Sum ?x ?y ?z } ;

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

DEFER: make-call-simp-rule
DEFER: make-exec-prop-rule

! Create rule for quotations
CHR: build-call-rule @ // { DefCallRule ?n ?s ?t f } { Marked ?n ?l } { Stack ?s ?a } { Stack ?t ?b } -- |
[| | store get values rest
 [ vars>> [ ?l in? ] all? ] filter
 :> body-chrs
 body-chrs [ id>> kill-chr ] each
 body-chrs [ constraint>> ] map
 [ Trans? ] reject
 ! [ constraint-type \ call = ] reject
 [ Stack? ] reject
 ! [ { [ Stack? ] [ s1>> { [ ?s == ] [ ?t == ] } 1|| not ] } 1&& ] reject
 P{ is ?rho ?a } prefix
 P{ is ?sig ?b } suffix
 :> body
 ?n Q?
 [
     { { call L{ ?n . ?rho } ?sig } }
     body
     ?n name>> make-call-simp-rule
 ] [ { { ?n ?rho ?sig } } body ?n make-exec-prop-rule ] if
 AddRule boa
] ;

! CHR: add-def-rule @ // { DefCallRule ?w ?s ?t ?b } -- |
! { TransRule { Trans ?s ?t ?w } ?b } ;

! DEFER: make-trans-rule

! CHR: add-program-rule @ // { TransRule { Trans ?s ?t ?w } ?b } -- |
! [ ?s ?t ?b ?w make-trans-rule AddRule boa ] ;

;

! * External

: build-quot ( quot -- chrs )
    quots swap BuildQuot boa 1array run-chr-query values rest ;

: build-quot-rule ( quot name -- chrs )
    swap BuildNamedCall boa 1array quots swap run-chr-query values rest ;

:: make-call-simp-rule ( heads body word -- rule )
    word name>> :> wname
    wname "-call" append :> rname
    heads 0 f body f named-chr new-chr rname >>rule-name ;

:: make-exec-prop-rule ( heads body word -- rule )
    word name>> :> wname
    wname "-exec" append :> rname
    heads 1 f body f named-chr new-chr rname >>rule-name ;

:: make-trans-rule ( sin send body word -- rule )
    word name>> :> wname
    wname "-call" append :> rule-name
    sin send word Q boa Trans boa 1array :> heads
    heads
    1 f body f
    named-chr new-chr
    rule-name >>rule-name
    ;

: build-word ( word -- chrs )
    [ def>> ] keep swap BuildExecRule boa 1array quots swap run-chr-query values rest ;
