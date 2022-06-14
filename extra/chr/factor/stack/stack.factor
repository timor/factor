USING: accessors arrays chr chr.factor chr.factor.defs chr.parser chr.state
classes.algebra combinators combinators.short-circuit effects generic.math
kernel kernel.private lists math math.parser quotations sequences strings terms
types.util words words.symbol ;

IN: chr.factor.stack


! * Util for effect/stack conversions

GENERIC: elt>var ( i elt -- obj )
M: f elt>var drop number>string "v" prepend utermvar ;
M: string elt>var nip utermvar ;
M: pair elt>var
    first2 drop elt>var ;

: elt-vars ( seq -- seq )
    [ swap elt>var ] map-index ;

! * Eval State model

PREDICATE: callable-word < word { [ symbol? not ] } 1&& ;

! Elements represent type expressions, which have "Have" semantics
TUPLE: Stack < chr-pred content ;
TUPLE: Eval < chr-pred code ;
TUPLE: Eval1 < chr-pred thing ;

! Effect Type
TUPLE: Effect < chr-pred in out ;

! Types
TUPLE: TypeOf < chr-pred var type ;

TUPLE: ExpectType < chr-pred stack types ;

CHRAT: chr-stack {  }

! ** Type stack operations


! *** Destructuring
CHR: did-expect-types @ // { ExpectType __ +nil+ } -- | ;
CHR: expecting-types @ // { ExpectType L{ ?x . ?xs } L{ ?y . ?ys } } -- |
{ ExpectType ?x ?y }
{ ExpectType ?xs ?ys } ;

! *** Asserting required types
CHR: check-expect-type @ // { ExpectType A{ ?x } A{ ?rho } } --
! Wrapping this to presever wrapper during expansion
[ { ?x } first dup wrapper? [ <wrapper> :>> ?tau ] [ :>> ?tau ] if ] |
! [ { ?x } first :>> ?tau ] |
[ ?tau ?rho class<= [ { ?tau ?rho "expect type failed" } throw ] unless f ] ;

CHR: establish-expect-type @ // { ExpectType ?x A{ ?rho } } -- |
[ ?x ?rho ==! ] ;

! ** Stack-state advancing

! Internal representation of sequence of words is list...
CHR: eval-quot @ // { Eval ?p } -- [ ?p callable? ] [ ?p >list :>> ?q ] |
{ Eval ?q } ;

! CHR: eval-done @ // { Eval +nil+ } -- | ;
CHR: eval-step @ // { Eval L{ ?x . ?xs } } -- |
{ Eval1 ?x } { Eval ?xs } ;

! *** Literals
CHR: eval-lit @ // { Eval1 ?x } { Stack ?y } -- [ ?x callable-word? not ] |
{ Stack L{ W{ ?x } . ?y } } ;

! *** Executable word with known effect
! NOTE: destructive!
CHR: ensure-stack @ { Eval1 ?x } { Stack ?y } // -- [ ?x defined-effect :>> ?e ]
[ ?e in>> :>> ?i ] [ ?y llength* ?i length < ] |
[| | ?i elt-vars <reversed> >list ?rho lappend :> lin
 [ ?y lin ==! ] ] ;

! NOTE: destructive!
CHR: ensure-declare-stack @ { Eval1 declare } { Stack L{ A{ ?a } . ?r } } // -- [ ?a length :>> ?n ] |
[| | ?n [ f elt>var ] { } map-integers <reversed> >list ?rho lappend :> lin
 [ ?r lin ==! ]
] ;

! *** Shuffle Word Eval
! NOTE: depends on ensured stack
CHR: eval-shuffle @ // { Eval1 ?w } { Stack ?y } -- [ ?w "shuffle" word-prop :>> ?e ] |
[| | ?y ?e in>> length lcut :> ( top rest )
 top list>array <reversed> :> vin
 vin ?e shuffle <reversed> >list rest lappend :> sout
 { Stack sout }
] ;

! ** Expected Types at word inputs
CHR: eval-declare @ // { Eval1 declare } { Stack L{ A{ ?a } . ?r } } -- [ ?a <reversed> >list :>> ?tau ] |
{ Stack ?r }
{ ExpectType ?r ?tau } ;

CHR: math-types @ { Eval1 ?w } { Stack ?y } // -- [ ?w math-generic? ] [ ?w stack-effect in>> length number <array> >list :>> ?tau ] |
{ ExpectType ?y ?tau } ;

! ** Higher-Order
CHR: eval-call @ // { Eval1 call } { Stack L{ ?q . ?rho } } -- |
{ Stack L{ ?q ?e . ?rho } }
{ ExpectType ?q callable }
{ TypeOf ?q ?e }
{ Eval1 call-effect } ;

! ** Finishing

CHR: close-effect @ // { Effect ?rho __ } { Eval +nil+ } { Stack ?sig } -- |
{ Effect ?rho ?sig } ;

;

TERM-VARS: ?s0 ;

: bq ( code -- res )
    P{ Effect ?s0 f }
    P{ Stack ?s0 }
    rot Eval boa 3array
    [ chr-stack swap run-chr-query store>> ] with-var-names ;
