USING: accessors arrays chr chr.comparisons chr.factor chr.parser chr.state
combinators effects kernel lists math.parser namespaces sequences sets terms
types.util words words.symbol ;

IN: chr.factor.direct

PREDICATE: quot-sym < word "quot-id" word-prop? ;
: <quot-sym> ( name -- word ) usym dup t "quot-id" set-word-prop ;

PREDICATE: callable-word < word { [ symbol? not ] [ quot-sym? not ] } 1&& ;
! PREDICATE: callable-word < word symbol? not ;

: stack-match ( stack-var elts rest -- chr )
    [ __ ] unless*
    [ >list ] dip list*
    <eq-constraint> ;


: elt-vars ( seq -- seq )
    [ swap dup pair? [ first ] when
      [ nip ] [ number>string "v" prepend ] if*
      uvar
      <term-var>
    ] map-index <reversed> ;

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
TUPLE: BuildNamedQuot < chr-pred name quot ;
! TUPLE: DefCallRule < chr-pred name start end ;
TUPLE: DefCallRule < chr-pred name start end body ;
TUPLE: SimpRule < chr-pred name heads body ;
TUPLE: TransRule < chr-pred head body ;
TUPLE: Mark < chr-pred val ;
TUPLE: Marked < chr-pred vals ;

CHRAT: quots { }
CHR: stack-match @ { Stack ?s ?a } // { Stack ?s ?b } -- | [ ?a ?b ==! ] ;
CHR: empty-quot @ // { Transeq ?s ?t [ ] } -- | [ ?s ?t ==! ] ;
CHR: destructure-quot @ // { Transeq ?s ?t ?p } -- [ ?p first :>> ?w ?p rest :>> ?q ?s seq-state :>> ?s0 3drop t ] |
{ Trans ?s ?s0 ?w }
{ Transeq ?s0 ?t ?q } ;

CHR: effect-predicate @ { Trans ?s ?t ?w } // -- [ ?w callable-word? ]
[ ?w stack-effect effect>stacks [ :>> ?a ] [ :>> ?b ] bi* 2drop t ]
|
{ Stack ?s ?a }
{ Stack ?t ?b }
[ ?a list>array* ?b list>array* append ?w prefix ] ;

CHR: infer-callable @ // { Trans ?s ?t ?q } -- [ ?q callable? ] [ "q" <quot-sym> :>> ?p ] |
{ Trans ?s ?t W{ ?p } }
{ BuildNamedQuot ?p ?q }
;

CHR: push-effect @ { Trans ?s ?t ?w } // -- [ ?w callable-word? not ] |
{ Stack ?s ?xs }
{ Stack ?t L{ ?w . ?xs } } ;


CHR: build-quot-body @ // { BuildQuot ?q } -- |
{ Transeq +top+ +end+ ?q } ;

CHR: build-named-def @ // { BuildNamedQuot ?n ?q } -- |
{ Transeq ?s ?t ?q }
{ Mark ?s }
{ Marked f }
{ DefCallRule ?n ?s ?t f } ;

CHR: mark-once @ { Mark ?x } // { Mark ?x } -- | ;
CHR: mark-trans @ { Mark ?s } { Trans ?s ?t __ } // -- | { Mark ?t } ;
CHR: mark-stack @ { Mark ?s } { Stack ?s ?x } // -- | [ ?x vars [ Mark boa ] map ] ;
CHR: collect-marks @ // { Marked ?a } { Mark ?x } -- [ ?a ?x suffix :>> ?b drop t ] | { Marked ?b } ;
CHR: build-call-rule @ // { DefCallRule ?n ?s ?t f } { Marked ?l } -- |
[| | store get values rest
 [ vars>> [ ?l in? ] all? ] filter :> body-chrs
 body-chrs [ id>> kill-chr ] each
 body-chrs [ constraint>> ] map :> body
 P{ DefCallRule ?n ?s ?t body }
] ;

CHR: add-def-rule @ // { DefCallRule ?w ?s ?t ?b } -- |
{ TransRule { Trans ?s ?t ?w } ?b } ;

;

: build-quot ( quot -- chrs )
    quots swap BuildQuot boa 1array run-chr-query values rest ;

: build-quot-rule ( quot name -- chrs )
    swap BuildNamedQuot boa 1array quots swap run-chr-query values rest ;

:: make-trans-rule ( sin send body word -- rule )
    word name>> :> wname
    wname "-call" append :> rule-name
    sin send word Trans boa 1array :> heads
    heads
    1 f body f
    named-chr new-chr
    rule-name >>rule-name
    ;

:: filter-marked-chrs ( marked def-rule chrs -- def-rule chrs )
    chrs [ vars [ marked in? ] all? ] filter
    def-rule swap ;

:: construct-def-rule ( def-rule chrs -- rule )
    def-rule [ name>> ] [ start>> ] [ end>> ] tri :> ( w s e )
    s e chrs w make-trans-rule ;

: extract-def-rule ( chrs -- rule )
    [ [ Marked? ] find vals>> swap ]
    [ remove-nth ] bi
    [ [ DefCallRule? ] find swap ]
    [ remove-nth ] bi
    filter-marked-chrs
    construct-def-rule
    ;

: infer-quot-rule ( quot -- sym rule )
    "quot" usym tuck build-quot-rule
    extract-def-rule ;
    ! "quot" usym tuck
    ! [

    !     build-quot-rule [ DefCallRule? ] partition
    !     [ first [ start>> ] [ end>> ] bi ] dip
    ! ] keep
    ! make-trans-rule ;
