USING: accessors arrays chr chr.comparisons chr.factor chr.parser chr.state
combinators effects kernel lists math.parser sequences sets terms types.util
words words.symbol ;

IN: chr.factor.direct

PREDICATE: callable-word < word symbol? not ;

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
    effect [ in-var>> ] [ out-var>> ] bi :> ( i o )
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

! Linear follow up
SYMBOL: ->

GENERIC: infer-1-chr ( sin out word -- chrs )
M: callable-word infer-1-chr ( sin sout word -- chrs )
    -rot 3array 1array ;

M:: object infer-1-chr ( sin sout obj -- chrs )
    "rho" utermvar :> rho
    P{ is sin rho }
    P{ is sout L{ obj . rho } }
    2array ;

: (infer-body-chrs) ( svar quot -- svar' chrs )
    [| s w |
     s seq-state :> sn
     s sn w infer-1-chr
     sn swap
    ] gather ;

:: make-word-rule ( sin send body wname -- rule )
    wname "-call" append :> rule-name
    wname sin send 3array 1array :> heads
    heads
    1 f body f
    named-chr new-chr
    rule-name >>rule-name
    ;

:: add-effect-chrs ( sin sout chrs effect -- sin sout chrs )
    sin sout
    2dup
    effect effect>stacks swapd
    [| s l | P{ is s l } ] 2bi@ 2array chrs append ;


:: infer-def-rule ( def effect name -- rule )
    "s0" utermvar dup def (infer-body-chrs)
    effect [ add-effect-chrs ] when*
    name make-word-rule ;

    ! [ "s0" utermvar dup ] 2dip
    ! [ drop def>> (infer-body-chrs) ]
    ! [ nip make-word-rule ] 2bi ;

: infer-word-rule ( word -- rule )
    [ def>> ] [ stack-effect ] [ name>> ] tri infer-def-rule ;

! : (infer-body-chrs) ( stack-var chrs quot -- stack-var chrs )
!     dup empty? [ drop ]
!     [| svar accum quot |
!      quot unclip-slice :> ( rest next )
!      next callable-word? dup :> exec?
!      [ next stack-effect effect>stacks ]
!      [ L{ } L{ next } ] if :> ( stack-in stack-out )
!      svar seq-state :> tvar
!      "rho" utermvar :> gvar
!      stack-in gvar lappend :> s1
!      stack-out gvar lappend :> s2
!      tvar
!      accum
!      svar s1 \ == 3array >quotation suffix
!      tvar s2 \ == 3array >quotation suffix
!      exec? [ { next svar tvar } suffix ] when
!      { -> svar tvar } suffix
!      rest (infer-body-chrs)
!     ] if ;
