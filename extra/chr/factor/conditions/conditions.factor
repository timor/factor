USING: chr chr.factor chr.factor.terms chr.parser chr.state kernel sequences
terms ;

IN: chr.factor.conditions

! * Condition system

! Escaped version of f

SINGLETON: F
TUPLE: Rule < chr-pred cond body ;
TUPLE: Mux < chr-pred cond val then else ;
TUPLE: ?: < chr-pred cond true false ;
TUPLE: Assume < chr-pred cond ;

TUPLE: --> < chr-pred cond consequence ;
TUPLE: \--> < chr-pred cond consequence ;

CHRAT: chr-cond {  }

! ! Kind of an embedded 3-SAT conversion...?
CHR: unique-and-1 @ And{ ?x ?y ?z } // And{ ?x ?y ?z  } -- | ;
CHR: unique-xor @ Xor{ ?x ?y ?z } // Xor{ ?x ?y ?z } -- | ;
CHR: useless-xor @ // Xor{ A{ f } A{ f } ?x } -- | ;
! CHR: redundant-and @ And{ ?x ?x ?x } // -- | ;
! CHR: unique-and-2 @ And{ ?x ?y ?z } // And{ ?y ?x ?z  } -- | ;
! CHR: and-simplify-3 @ // And{ ?x ?x ?z } -- | [ ?x ?z ==! ] ;
! CHR: and-tautology-1 @ And{ true true true } // -- | ;
! CHR: and-tautology-2 @ And{ false true false } // -- | ;
! CHR: and-tautology-3 @ And{ true false false } // -- | ;
! CHR: and-tautology-4 @ And{ false false false } // -- | ;
! CHR: and-contradiction-1 @ And{ true false true } // -- | false ;
! CHR: and-contradiction-2 @ And{ false true true } // -- | false ;
! CHR: and-contradiction-3 @ And{ false false true } // -- | false ;
! CHR: and-contradiction-4 @ And{ true true false } // -- | false ;
! CHR: and-result-1 @ // And{ true true ?x } -- | [ ?x true ==! ] ;
! CHR: and-result-2 @ And{ false ?y ?z } // -- | [ ?z false ==! ] ;
! CHR: and-result-3 @ And{ ?y false ?z } // -- | [ ?z false ==! ] ;
! CHR: and-tluser @ And{ ?x ?y true } // -- | [ ?x true ==! ] [ ?y true ==! ] ;
! CHR: and-simplify-1 @ // And{ true ?x ?z } -- | [ ?x ?z ==! ] ;
! CHR: and-simplify-2 @ // And{ ?x true ?z } -- | [ ?x ?z ==! ] ;
! CHR: and-tautology-2 @ And{ false true false } // -- | ;
! CHR: and-tautology-3 @ And{ true false false } // -- | ;
! CHR: and-tautology-4 @ And{ false false false } // -- | ;
! CHR: and-contradiction-1 @ And{ true false true } // -- | false ;
! CHR: and-contradiction-2 @ And{ false true true } // -- | false ;
! CHR: and-contradiction-3 @ And{ false false true } // -- | false ;
! CHR: and-contradiction-4 @ And{ true true false } // -- | false ;
! CHR: and-result-1 @ True{ ?x } True{ ?y } // And{ ?x ?y ?z } -- | True{ ?z } ;
! CHR: and-simplify-1 @ Not{ ?x } // And{ ?x ?z ?z } -- |
! CHR: and-simplify-1 @ True{ ?x } // And{ ?x ?y ?z } -- | [ ?y ?z ==! ] ;
! CHR: and-simplify-2 @ True{ ?y } // And{ ?x ?y ?z } -- | [ ?x ?z ==! ] ;
! CHR: and-result-2 @ True{ ?x } Xor{ ?x ?y } // And{ ?x ?y ?z } -- | Xor{ ? }
! CHR: and-result-2 @ False{ ?x } False{ ?y } // And{ ?x ?y ?z } -- | False{ ?z } ;
! CHR: and-result-3 @ False{ ?y } False{ ?x } // And{ ?x ?y ?z } -- | False{ ?z } ;
! CHR: and-tluser @ True{ ?z } // And{ ?x ?y ?z } -- | { True ?x } { True ?y } ;

! TBR?
! CHR: contradiction @ { True ?c } { False? ?c } // -- | false ;

! CHR: value-tautology-1 @ { True true } // -- | ;
! CHR: value-tautology-2 @ { False false } // -- | ;
! CHR: value-contradiction-1 @ { True false }  // -- | false ;
! CHR: value-contradiction-2 @ { False true }  // -- | false ;

! CHR: assume-true @ // { True ?c } { Assume ?c } -- | [ ?c true ==! ] ;
! CHR: assume-false @ // { False ?c } { Assume ?c } -- | [ ?c false ==! ] ;
! CHR: known-xor-value-1 @ // { Xor ?x true } -- | [ ?x false ==! ] ;
! CHR: known-xor-value-2 @ // { Xor true ?y } -- | [ ?y false ==! ] ;
! CHR: known-xor-value-3 @ // { Xor ?x false } -- | [ ?x true ==! ] ;
! CHR: known-xor-value-4 @ // { Xor false ?y } -- | [ ?y true ==! ] ;

! NOTE: f here is empty conjunction, which means logical true!
CHR: simplify-and-value1 @ // { And ?x A{ f } ?z } -- | [ ?x ?z ==! ] ;
CHR: simplify-and-value2 @ // { And A{ f } ?y ?z } -- | [ ?y ?z ==! ] ;

! * Cond Scopes
CHR: duplicate-constraints @ { C ?c ?x } // { C ?c ?x } -- | ;
CHR: pull-tautology @ // { C A{ f } ?k } -- | [ ?k ] ;
CHR: useless-true @ // { True A{ f } } -- | ;
CHR: redundant-defs @ // { C True{ ?c } ?p } { C False{ ?c } ?p } -- | [ ?p ] ;
! TODO: switch to set semantics!
CHR: contradicting-defs @ // { C True{ ?c } P{ C False{ ?c } __ } } -- | ;
CHR: contradicting-defs-2 @ // { C False{ ?c } P{ C True{ ?c } __ } } -- | ;
CHR: implied-defs @ // { C True{ ?c } P{ C True{ ?c } ?p } } -- | [ ?p ] ;
CHR: implied-defs-2 @ // { C False{ ?c } P{ C False{ ?c } ?p } } -- | [ ?p ] ;


CHR: expand-conjunction @ // { C ?p ?b } -- [ ?b sequence? ] |
[| |
 ?b [ ?p swap C boa ] map
] ;

;
