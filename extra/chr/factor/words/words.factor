USING: accessors arrays assocs chr.comparisons chr.factor chr.factor.compiler
chr.factor.conditions chr.factor.infer chr.factor.stack chr.factor.types
chr.parser chr.state classes classes.builtin combinators.short-circuit
continuations effects generic hashtables kernel kernel.private layouts lists
macros.expander make math math.parser namespaces quotations sequences sets terms
types.util words ;

IN: chr.factor.words

TUPLE: Shuffle < trans-pred mapping ;
TUPLE: ApplyWordRules < trans-pred w ;
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

: effect>vars ( effect -- in-seq out-seq )
    [ in>> elt-vars ]
    [ out>> elt-vars ] bi ;

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
! CHR{ { Dead ?x } // { AskLit ?x __ } -- | }
! CHR{ { AbsurdState ?s } // { Word ?s __ __ } -- | }
! CHR: absurd-call @ { AbsurdState ?s } // { Call ?s __ ?i ?o } -- |
!      [ V{ } clone ?i [ Dead boa over push ] leach*
!        ?o [ Dead boa over push ] leach* ]
   ! ;
! CHR{ { AbsurdState ?s } // { FoldCall ?s __ __ __ } -- | }

! ** Primitives

TUPLE: DropValue < state-pred x ;
TUPLE: DupValue < state-pred x y ;

! CHR{ // { DupValue ?s ?x ?y } -- | { Cond ?s { Dup ?x ?y } } }
! CHR{ // { DropValue ?s ?x } -- | { Cond ?s { Drop ?x } } }
CHR{ // { DupValue ?s ?x ?y } -- | { --> ?s P{ Dup ?x ?y } } }
CHR{ // { DropValue ?s ?x } -- | { --> ?s P{ Drop ?x } } }

! FIXME: make a shuffle generator which correctly tracks dups and drops
CHR: infer-dup @ // { Word ?s ?t dup } -- |
     ! { Stack ?s L{ ?x . ?rho } }
     ! { Stack ?t L{ ?y ?x . ?rho } }
{ StackOp ?s ?t L{ ?x . ?rho } L{ ?y ?x . ?rho } }
     { DupValue ?s ?x ?y } ;

CHR: infer-dupd @ // { Word ?s ?t dupd } -- |
{ StackOp ?s ?t L{ ?y ?x . ?rho } L{ ?y ?x ?xs } }
{ DupValue ?s ?x ?xs } ;

CHR: infer-over @ // { Word ?s ?t over } -- |
     ! { Stack ?s L{ ?y ?x . ?rho } }
     ! { Stack ?t L{ ?z ?y ?x . ?rho } }
     { StackOp ?s ?t L{ ?y ?x . ?rho } L{ ?xs ?y ?x . ?rho } }
     { DupValue ?s ?x ?xs } ;

CHR: curry-effect @ // { Word ?s ?t curry } -- |
! { Stack ?s L{ ?p ?parm . ?rho } }
! { Stack ?t L{ L{ ?parm . ?p } . ?rho } }
{ StackOp ?s ?t L{ ?p ?parm . ?rho } L{ L{ ?parm . ?p } . ?rho } }
{ Effect ?p L{ ?parm . ?a } ?b }
    ;

CHR: compose-effect @ // { Word ?s ?t compose } --  |
     { StackOp ?s ?t L{ ?q ?p . ?rho } L{ { ?p ?q } . ?rho } }
     { Effect ?p ?a ?b }
     { Effect ?q ?b ?c }
     ! { Stack ?s L{ ?q ?p . ?rho } }
     ! { Stack ?t L{ { ?p ?q } . ?rho } }
   ;

CHR: drop-prim @ // { Word ?s ?t drop } -- |
     ! { Stack ?s L{ ?x . ?rho } }
! { Stack ?t ?rho }
{ StackOp ?s ?t L{ ?x . ?rho } ?rho }
{ DropValue ?s ?x } ;

CHR: nip-prim @ // { Word ?s ?t nip } -- |
     ! { Stack ?s L{ ?y ?x . ?rho } }
     ! { Stack ?t L{ ?y . ?rho } }
{ StackOp ?s ?t L{ ?y ?x . ?rho } L{ ?y . ?rho } }
{ DropValue ?s ?x }
   ;

CHR: pick-prim @  // { Word ?s ?t pick } -- |
     ! { Stack ?s L{ ?z ?y ?x . ?rho } }
     ! { Stack ?t L{ ?w ?z ?y ?x . ?rho } }
     { StackOp ?s ?t L{ ?z ?y ?x . ?rho } L{ ?w ?z ?y ?x . ?rho } }
     { DupValue ?s ?x ?w }
   ;


CHR: declare-prim @ // { Word ?s ?t declare } -- { Stack ?s L{ ?c ?x . ?rho } } |
{ Stack ?t L{ ?x . ?rho } }
{ Type ?x ?tau }
{ _is ?c ?sig }
{ Subtype ?tau ?sig } ;

! ** Macros
TUPLE: FoldMacroEffect < trans-pred exec effect ;

! TUPLE: AskLits < state-pred lits parms ;
CHR: expand-macro-quot @ // { Word ?r ?u ?w } -- [ ?w macro-quot :>> ?p ] |
[| | ?w macro-effect "mx" <array> "quot" 1array <effect> :> e
 ! n-in [ "mparm" uvar <term-var> ] replicate :> in-parms
 ! n-in [ "mlit" uvar <term-var> ] replicate :> in-lits
 ! in-parms <reversed> >list ?rho lappend :> in-vars
 ! L{ ?q . ?rho } :> out-vars
 {
     ! { Stack ?s ?rho }
     ! { InsertStates ?r { ?s ?t } }
     ! { FoldMacroEffect ?r ?s ?p e }
     { FoldMacroEffect ?r ?u ?p e }
     ! { StackOp ?s ?t L{ ?q . ?rho } ?rho }
     ! { Instance ?q callable }
     ! { Stack ?s in-vars }
     ! { AddLink ?s ?s0 }
     ! { InferBetween ?s ?s0 q }
     ! { AddLink ?s0 ?t }
     ! { InferBetween ?s ?s0 q }
     ! { InlineUnknown ?t ?u ?q }
     ! { FoldQuot ?s ?t in-parms q }
 }
] ;

! TODO: move to expander!
TUPLE: FoldScope < Scope ;
CHR: inline-fold-quot @ // { FoldMacroEffect ?r ?u ?q ?e } --
[ ?e in>> elt-vars :>> ?i ]
! [ ?i ?rho lappend :>> ?a ]
! [ L{ ?q . ?rho } :>> ?b ]
|
{ InsertStates ?r { ?s0 } }
[| | ?i >list ?rho lappend :> a
 { StackOp ?r ?s0 a ?rho }
]
{ InlineUnknown ?s0 ?u ?p }
{ FoldCall ?s0 ?q ?i { ?p }  }
;



! { Scope ?r ?u ?a ?b { ?s0 ?t } }
! { Stack ?r ?u ?a }
! { Stack ?s0 ?rho }
! [
!     | |
!  ?e in>> >list ?rho lappend :> lin
!  ?e out>> >list ?rho lappend :> lout
!  { Scope ?r ?u lin lout { ?s0 ?t } }
!  { Stack ?r lin }
!  { Stack ?s0  }
! ]
! { FoldCall }
! { InlineQuot ?r ?u [ ?q call call ] }
! ;

! ** General effect assumption
CHR: assume-word-effect @ { Word ?s ?t ?w } // -- |
[| | ?w chrat-effect :> e { AssumeWordEffect ?s ?t ?w e } ] ;

! ** Shuffle
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
          li [
              ! "i" swap number>string append "_" append uvar <term-var>
              ?s swap pos-var
          ] { } map-integers :> v-in
          v-in >list ?rho lappend :> sin
          m <reversed> [ li swap - 1 - v-in nth ] map >list ?rho lappend :> sout
          { StackOp ?s ?t sin sout }
          ! Stack boa 2array
      ] if-empty ] }

! TODO Math words
! CHR: { { Word ?s ?t ?w } // -- }

! CHR{ // { Word ?s ?t ?w } -- [ ?w primitive? ] | { Prim ?s ?t ?w } }

! ** Inline Words
CHR{ // { InlineWord ?s ?t ?w } -- | [| | ?w def>> :> def { InlineCall ?s ?t ?w def } ] }

! CHR{ // { Word ?s ?t ?w } -- [ ?w generic? ] | { Generic ?s ?t ?w } }
! CHR{ // { Word ?s ?t ?w } -- [ ?w method? ] | { Method ?s ?t ?w } }

! ** General Word Rules
! FIXME: apply all rules
CHR{ { Word ?s ?t ?w } // --
     ! [ ?w generic? not ]
     |
     { ApplyWordRules ?s ?t ?w } }

! ** Foldable Words

! Alternatively, only try folding if we have a top literal?
! CHR{ { Word ?s ?t ?w } { Stack ?s L{ ?x . __ } } { Lit ?x __ } // -- [ ?w foldable? ] |
! CHR: try-fold-word @ { Word ?s ?t ?w } { Lit ?x __ } // -- [ ?w foldable? ] { Stack ?s L{ ?x . __ } } |
! CHR: try-fold-word @ { Word ?s ?t ?w } // -- [ ?w foldable? ] |
!      [| | ?w stack-effect :> e { FoldMacroEffect ?s ?t ?w e } ] ;

! NOTE: Assuming that foldable effects are always bounded!
! CHR: try-fold @ { FoldMacroEffect ?s ?t ?w ?e } // -- [ ?e known? ] |
!      [| | ?e in>> elt-vars dup
!       >list ?rho lappend :> stack-in
!       ! <reverse> [ number>string "lv" prepend uvar <term-var> 2array ] map :> var-map-in
!       <reversed> dup :> var-in
!       length [ number>string "lv" prepend uvar <term-var> ] { } map-integers :> lit-in
!       ?e out>> elt-vars dup
!       >list ?rho lappend :> stack-out
!       reverse :> var-out
!       { { Stack ?s stack-in }
!         { Stack ?t stack-out }
!         { FoldCall ?s ?w lit-in var-out }
!       }
!       ! var-in [ number>string "lv" prepend uvar <term-var> AskLit boa ] map-index append
!       var-in lit-in [ AskLit boa ] 2map append
!      ]
!    ;

! Theoretically this is dead, because we don't expect a value to be used twice
! CHR{ // { Lit ?x ?v } { AskLit ?x ?a } -- | [ ?a ?v ==! ] { Dead ?x } }

! CHR: do-fold-call @ // { Call ?s ?w __ __ } { FoldMacroEffect ?s __ __ __ } { FoldCall ?s ?w ?i ?o } -- [ ?i [ known? ] all? ] |
!     [ ?i [ known ] map ?w 1quotation with-datastack
!       ?o swap [ Lit boa ] 2map
!     ] ;
CHR: try-foldable-call @ { InferMode } { is ?x A{ __ } } { Call ?s ?w L{ ?x . ?i } ?o } // -- [ ?w foldable? ] |
[| | ?w stack-effect effect>vars :> ( vin vout )
 vin >list __ lappend :> lin
 vout >list __ lappend :> lout
 { lin lout } { L{ ?x . ?i } ?o } ==!
 ?w 1quotation :> mquot
 { FoldCall ?s mquot vin vout } 2array
] ;


ERROR: folding-error inputs quot error ;

CHR: do-fold-call @ // { Call ?s __ __ __ } { FoldCall ?s ?w A{ ?i } ?o } -- |
    [ ?i <reversed> ?w [ with-datastack ] [ folding-error ] recover
      ?o swap [ is boa ] 2map
    ] ;

CHR: get-fold-args @ { is ?x ?v } // { FoldCall ?s ?w ?i ?o }  -- [ ?x ?i in? ] |
[ ?s ?w ?i ?v ?x associate substitute ?o FoldCall boa ] ;

! CHR: do-fold-quot @ // { FoldMacroEffect ?s ?t __ ?e } { FoldCall ?s ?q ?i ?o } -- [ ?q callable? ] [ ?i [ known? ] all? ] |
! [ ?i [ known ] map ?q with-datastack
!   ?o swap [ Lit boa ] 2map
! ]
! [ ?s ?t ?e effect>stacks [ ?rho lappend ] bi@ StackOp boa ]
!     ;

! ** Anything else

CHR: normal-word-call @ // { Word ?s ?t ?w } -- { Stack ?s ?i } ! { Stack ?t ?o }
|
     ! { Stack ?s ?i }
     ! { Stack ?t ?o }
     { Call ?s ?w ?i ?o }
     { Stack ?t ?o }
  ;

! Compilation stuff
TUPLE: TagTest < val-pred in-obj ;

CHR: insert-tag-check @ // { ApplyWordRules ?s ?t tag } -- { Stack ?s L{ ?x . __ } } |
{ Stack ?t L{ ?n . __ } }
! { Type ?x ?tau }
! { _is ?c ?tau }
{ TagTest ?n ?x }
;

CHR: known-tag @ { Type ?x A{ ?v } } // { TagTest ?n ?x } -- [ ?v builtin-class? ] |
[ ?n ?v tag is boa  ] ;

CHR: expand-partial-tag-rules @ { Type ?x ?tau } { Subtype ?tau A{ ?sig } } // { TagTest ?n ?x } -- |
[ type-numbers get
  [| tau n | { <--> P{ Type ?x tau } P{ is ?n n } } ] { } assoc>map
] ;

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

! Instance checks
CHR: instance-test @ { ApplyWordRules ?s ?t instance? } // -- { Stack ?s L{ ?c ?x . __ } } |
{ _is ?c ?tau }
{ Stack ?t L{ ?b . __ } }
{ Type ?b boolean }
{ <--> P{ is ?b W{ f } } P{ Not P{ Type ?x ?tau } } }
{ <--> P{ Not P{ is ?b W{ f } } } P{ Type ?x ?tau } }
! { <--> P{ is ?b t } P{ Type ?x ?tau } }
;

! General rules

! CHR: predicating-rules @ //


CHR: instantiate-rules @ // { ApplyWordRules ?s ?t ?w } -- [ ?w generic? not ] |
[ ?s ?t ?w instantiate-word-rules ] ;

;
