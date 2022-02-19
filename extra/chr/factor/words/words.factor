USING: accessors arrays assocs chr.factor chr.factor.conditions chr.parser
chr.state combinators.short-circuit continuations effects generic generic.math
kernel lists math math.parser quotations sequences sets terms types.util words ;

IN: chr.factor.words

TUPLE: Shuffle < trans-pred mapping ;
TUPLE: ApplyWordRules < trans-pred w ;
TUPLE: AskLit < Lit ;
TUPLE: FoldCall < Call ;


GENERIC: chrat-effect ( word -- effect )
CONSTANT: effect-overrides H{
    { dip ( ..a x quot: ( ..a -- ..b ) -- ..b x ) }
    { call ( ..a quot: ( ..a -- ..b ) -- ..b ) }
}
M: word chrat-effect
    { [ effect-overrides at ] [ stack-effect ] } 1|| ;


GENERIC: chrat-in-types ( word -- seq/f )

M: word chrat-in-types
    "input-classes" word-prop ;

! M: method chrat-in-types
!     dup "method-generic" word-prop dup single-generic?
!     [ [ "method-class" word-prop ] [ dispatch# ] bi* dup 1 + object <array> [ set-nth ] keep ]
!     [ 2drop f ] if ;

GENERIC: chrat-out-types ( word -- seq/f )

M: word chrat-out-types
    "default-output-classes" word-prop ;

! Note: providing values is known upper bound!
M: math-generic chrat-out-types drop number 1array ;

: chrat-methods ( word -- seq/f )
    "methods" word-prop ;

: linear-shuffle? ( effect -- ? )
    [ in>> ] [ out>> ] bi { [ [ length ] same? ] [ set= ] } 2&& ;

: elt-vars ( seq -- seq )
    [ swap dup pair? [ first ] when
      [ nip ] [ number>string "v" prepend ] if*
      uvar
      <term-var>
    ] map-index <reversed> ;


CHRAT: chrat-words {  }

! Cleaning up
CHR{ { Dead ?x } // { AskLit ?x __ } -- | }
CHR{ { AbsurdState ?s } // { Word ?s __ __ } -- | }
CHR: absurd-call @ { AbsurdState ?s } // { Call ?s __ ?i ?o } -- |
     [ V{ } clone ?i [ Dead boa over push ] leach*
       ?o [ Dead boa over push ] leach* ]
   ;
CHR{ { AbsurdState ?s } // { FoldCall ?s __ __ __ } -- | }

! primitives

CHR: infer-dup @ // { Word ?s ?t dup } -- |
     { Stack ?s L{ ?x . ?rho } }
     { Stack ?t L{ ?y ?x . ?rho } }
     { Dup ?s ?x ?y } ;

CHR: infer-over @ // { Word ?s ?t over } -- |
     { Stack ?s L{ ?y ?x . ?rho } }
     { Stack ?t L{ ?z ?y ?x . ?rho } }
     { Dup ?s ?x ?z } ;

CHR: curry-effect @ // { Word ?s ?t curry } -- |
     { Stack ?s L{ ?p ?parm . ?rho } }
     { Effect ?p L{ ?parm . ?a } ?b }
     { Stack ?t L{ L{ ?parm . ?p } . ?rho } } ;

CHR{ // { Word ?s ?t compose } -- |
     { Stack ?s L{ ?q ?p . ?rho } }
     { Effect ?p ?a ?b }
     { Effect ?q ?b ?c }
     { Stack ?t L{ { ?p ?q } . ?rho } }
   }

CHR{ // { Word ?s ?t drop } -- |
     { Stack ?s L{ ?x . ?rho } }
     { Stack ?t ?rho }
     { Drop ?s ?x } }

CHR{ // { Word ?s ?t nip } -- |
     { Stack ?s L{ ?y ?x . ?rho } }
     { Stack ?t L{ ?y . ?rho } }
     { Drop ?s ?x }
   }

CHR{ // { Word ?s ?t pick } -- |
     { Stack ?s L{ ?z ?y ?x . ?rho } }
     { Stack ?t L{ ?w ?z ?y ?x . ?rho } }
     { Dup ?s ?x ?w }
   }


CHR: assume-word-effect @ { Word ?s ?t ?w } // -- |
[| | ?w chrat-effect :> e { AssumeEffect ?s ?t e } ] ;

CHR: infer-shuffle @ // { Word ?s ?t ?w } -- [ ?w "shuffle" word-prop? [ linear-shuffle? ] [ f ] if* ] |
[ ?s ?t ?w "shuffle" word-prop shuffle-mapping Shuffle boa ] ;

! TODO Math words
! CHR: { { Word ?s ?t ?w } // -- }

! CHR{ // { Word ?s ?t ?w } -- [ ?w primitive? ] | { Prim ?s ?t ?w } }

CHR{ // { InlineWord ?s ?t ?w } -- | [| | ?w def>> :> def { InlineCall ?s ?t ?w def } ] }

! CHR{ // { Word ?s ?t ?w } -- [ ?w generic? ] | { Generic ?s ?t ?w } }
! CHR{ // { Word ?s ?t ?w } -- [ ?w method? ] | { Method ?s ?t ?w } }

! FIXME: apply all rules
CHR{ { Word ?s ?t ?w } // -- [ ?w generic? not ] |
     { ApplyWordRules ?s ?t ?w } }

! Folding


! Alternatively, only try folding if we have a top literal?
CHR{ { Word ?s ?t ?w } { Stack ?s L{ ?x . __ } } { Lit ?x __ } // -- [ ?w foldable? ] |
     [| | ?w stack-effect in>> elt-vars dup
      >list ?rho lappend :> stack-in
      ! <reverse> [ number>string "lv" prepend uvar <term-var> 2array ] map :> var-map-in
      <reversed> dup :> var-in
      length [ number>string "lv" prepend uvar <term-var> ] { } map-integers :> lit-in
      ?w stack-effect out>> elt-vars dup
      >list ?sig lappend :> stack-out
      reverse :> var-out
      { { Stack ?s stack-in }
        { Stack ?t stack-out }
        { FoldCall ?s ?w lit-in var-out }
      }
      ! var-in [ number>string "lv" prepend uvar <term-var> AskLit boa ] map-index append
      var-in lit-in [ AskLit boa ] 2map append
     ]
   }

! Theoretically this is dead, because we don't expect a value to be used twice
CHR{ // { Lit ?x ?v } { AskLit ?x ?a } -- | [ ?a ?v ==! ] { Dead ?x } }

CHR: do-fold-call @ // { Call ?s __ __ __ } { FoldCall ?s ?w ?i ?o } -- [ ?i [ known? ] all? ] |
    [ ?i [ known ] map ?w 1quotation with-datastack
      ?o swap [ Lit boa ] 2map
] ;

! Anything else

CHR{ // { Word ?s ?t ?w } -- |
     { Stack ?s ?i }
     { Stack ?t ?o }
     { Call ?s ?w ?i ?o } }

;
