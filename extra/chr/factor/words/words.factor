USING: accessors arrays assocs chr.factor chr.factor.conditions
chr.factor.control chr.factor.infer chr.factor.stack chr.parser chr.state
combinators.short-circuit continuations effects generic kernel lists
macros.expander make math math.parser quotations sequences sets terms types.util
words ;

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

! ! Note: providing values is known upper bound!
! M: math-generic chrat-out-types drop number 1array ;

: chrat-methods ( word -- seq/f )
    "methods" word-prop ;

: linear-shuffle? ( effect -- ? )
    [ in>> ] [ out>> ] bi { [ [ length ] same? ] [ set= ] } 2&& ;

: effect>stacks ( effect -- lin lout )
    [ in>> elt-vars >list ]
    [ out>> elt-vars >list ] bi ;

M: Call state-depends-on-vars
    [
        [ in>> known [ , ] leach* ]
        [ out>> known [ , ] leach* ] bi
    ] { } make ;

CHRAT: chrat-words {  }

! Cleaning up
CHR{ { Dead ?x } // { AskLit ?x __ } -- | }
! CHR{ { AbsurdState ?s } // { Word ?s __ __ } -- | }
CHR: absurd-call @ { AbsurdState ?s } // { Call ?s __ ?i ?o } -- |
     [ V{ } clone ?i [ Dead boa over push ] leach*
       ?o [ Dead boa over push ] leach* ]
   ;
! CHR{ { AbsurdState ?s } // { FoldCall ?s __ __ __ } -- | }

! primitives

TUPLE: DropValue < state-pred x ;
TUPLE: DupValue < state-pred x y ;

CHR{ // { DupValue ?s ?x ?y } -- | { Cond ?s { Dup ?x ?y } } }
CHR{ // { DropValue ?s ?x } -- | { Cond ?s { Drop ?x } } }

CHR: infer-dup @ // { Word ?s ?t dup } -- |
     { Stack ?s L{ ?x . ?rho } }
     { Stack ?t L{ ?y ?x . ?rho } }
     { DupValue ?s ?x ?y } ;

CHR: infer-over @ // { Word ?s ?t over } -- |
     { Stack ?s L{ ?y ?x . ?rho } }
     { Stack ?t L{ ?z ?y ?x . ?rho } }
     { DupValue ?s ?x ?z } ;

CHR: curry-effect @ // { Word ?s ?t curry } -- |
     { Stack ?s L{ ?p ?parm . ?rho } }
     { Effect ?p L{ ?parm . ?a } ?b }
     { Stack ?t L{ L{ ?parm . ?p } . ?rho } } ;

CHR: compose-effect @ // { Word ?s ?t compose } -- |
     { Stack ?s L{ ?q ?p . ?rho } }
     { Effect ?p ?a ?b }
     { Effect ?q ?b ?c }
     { Stack ?t L{ { ?p ?q } . ?rho } }
   ;

CHR: drop-prim @ // { Word ?s ?t drop } -- |
     { Stack ?s L{ ?x . ?rho } }
     { Stack ?t ?rho }
     { DropValue ?s ?x } ;

CHR: nip-prim @ // { Word ?s ?t nip } -- |
     { Stack ?s L{ ?y ?x . ?rho } }
     { Stack ?t L{ ?y . ?rho } }
     { DropValue ?s ?x }
   ;

CHR: pick-prim @  // { Word ?s ?t pick } -- |
     { Stack ?s L{ ?z ?y ?x . ?rho } }
     { Stack ?t L{ ?w ?z ?y ?x . ?rho } }
     { DupValue ?s ?x ?w }
   ;

! Macros
! TUPLE: AskLits < state-pred lits parms ;
CHR: expand-macro-quot @ // { Word ?s ?t ?w } -- [ ?w macro-quot ] |
[| | ?w macro-effect :> n-in
 n-in [ "mparm" uvar <term-var> ] replicate :> in-parms
 n-in [ "mlit" uvar <term-var> ] replicate :> in-lits
 in-parms <reversed> >list ?rho lappend :> in-vars
 ! L{ ?q . ?rho } :> out-vars
 ?w macro-quot :> q
 {
     { Instance ?q callable }
     { Stack ?s in-vars }
     { AddLink ?s ?s0 }
     ! { AddLink ?s0 ?t }
     { Stack ?s0 L{ ?q . ?rho } }
     { InferBetween ?s ?s0 q }
     { InlineUnknown ?s0 ?t ?q }
     ! { FoldQuot ?s ?t in-parms q }
 }
] ;

CHR: assume-word-effect @ { Word ?s ?t ?w } // -- |
[| | ?w chrat-effect :> e { AssumeEffect ?s ?t e } ] ;

CHR: infer-shuffle @ // { Word ?s ?t ?w } -- [ ?w "shuffle" word-prop? [ linear-shuffle? ] [ f ] if* ] |
[ ?s ?t ?w "shuffle" word-prop shuffle-mapping Shuffle boa ] ;

: pos-var ( stack-var n -- var )
    [ name>> "_i" append ] dip number>string append
    <term-var> ;

: affine-shuffle? ( mapping -- ? )
    duplicates empty? ;

CHR{ // { Shuffle ?s ?t ?m } -- [ ?m known? ] |
     [| | ?m known dup :> m
      ! dup length 1 - :> lo
      dup length :> lo
      [ f ]
      [
          supremum 1 + :> li
          ?s li [
              ! "i" swap number>string append "_" append uvar <term-var>
              ?s swap pos-var
          ] { } map-integers :> v-in
          v-in >list ?rho lappend Stack boa
          ?t m <reversed> [ li swap - 1 - v-in nth ] map >list ?rho lappend Stack boa 2array
      ] if-empty ] }

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

! Compilation stuff
CHR: primitive-rules @ // { ApplyWordRules ?s ?t ?w } -- [ ?w primitive? ] |
! NOTE Assuming all primitive effects here are not broken!
[ ?w stack-effect
  [ effect>stacks [ ?rho lappend ?s swap Stack boa ] [ ?sig lappend ?t swap Stack boa ] bi* ]
  [ bivariable-effect?
    [ 2array ]
    [ [ ?rho ?sig ==! ] 3array ] if
  ] bi
]
    ;

! Insert at least one dummy state to prevent hooking into the top node with Entry specs
! CHR: instantiate-rules @ // { ApplyWordRules ?s ?t ?w } -- |
! ! { Stack ?s ?rho }
! ! { Stack ?s0 ?rho } { AddLink ?s ?s0 }
! ! [ ?s0 ?t ?w instantiate-word-rules ]
! [ ?s ?t ?w instantiate-word-rules ] ;

;
