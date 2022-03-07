USING: accessors chr.comparisons chr.factor chr.factor.conditions
chr.factor.stack chr.modular chr.parser chr.state kernel lists terms ;

IN: chr.factor.data-flow

! TUPLE: SplitStack < state-pred stack-in stack-out1 stack-out2 ;
TUPLE: SplitStack < Split ;
TUPLE: JoinStack < Join ;

! ** Data Flow
CHRAT: data-flow { Effect Copy Split Dup }

! Remove dropped literals
! CHR{ // { Drop ?x } { Lit ?x __  } -- | { Dead ?x } }

! *** Sanity checks
! CHR{ { Drop ?x } { Drop ?x } // -- | [ "double drop" throw ] }
CHR{ { Drop ?x } // { Drop ?x } -- | }
! CHR{ { Dup ?x ?y } { Dup ?x ?y } // -- | [ "douple dup" throw ] }
CHR{ { Dup ?x ?y } // { Dup ?x ?y } -- | }
CHR{ { Dup ?x ?x } // -- | [ "self-dup" throw ] }

CHR{ // { Dup ?x ?y } { Drop ?y } -- | [ ?x ?y ==! ] }
CHR{ // { Dup ?x ?y } { Drop ?x } -- | [ ?x ?y ==! ] }

CHR{ { Dup ?x ?y } // { ask { Copy ?x ?y } } -- | { entailed { Copy ?x ?y } } }

CHR: dup-literal @ { Dup ?x ?y } { is ?x A{ ?v } } // -- | { is ?y ?v } ;
! CHR{ { Split __ ?a ?x ?y } // { ask { Copy ?a ?y } } -- | { entailed { Copy ?a ?y } } }
! CHR{ { Split __ ?a ?x ?y } // { ask { Copy ?a ?x } } -- | { entailed { Copy ?a ?y } } }
! CHR{ { Join ?c ?x ?y } // { ask { Copy ?c ?y } } -- | { entailed { Copy ?c ?y } } }
! CHR{ { Join ?c ?x ?y } // { ask { Copy ?c ?x } } -- | { entailed { Copy ?c ?x } } }

! CHR{ { Effect ?x ?a ?b } // { Effect ?x ?a ?b } -- | }

! NOTE: This is tricky.  The idea is that any duplication is actually performed correctly on the stack?
! CHR: similar-effect-left @
!  { Dup ?x ?y } { Effect ?y L{ ?parm . ?a } ?b } // { Effect ?x ?c ?d } -- [ ?c known term-var? ] |
!      { Effect ?x L{ ?v . ?r } ?s }
!    ;

! CHR: copy-effect-left @
! { Dup ?x ?y } { Effect ?y ?a ?b } // -- [ ?a known term-var? ]
! | { Effect ?x ?c ?d } ;

! CHR: similar-effect-right @
! { Dup ?x ?y } { Effect ?x L{ ?parm . ?a } ?b } // { Effect ?y ?c ?d } -- [ ?c known term-var? ] |
! { Effect ?y L{ ?v . ?r } ?s }
!     ;

! CHR: make-dup-right @ { Dup L{ ?a . ?b } ?y } // -- [ ?y known term-var? ] |
! { Dup L{ ?a . ?b } L{ ?c . ?d } } [ ?y L{ ?c . ?d } ==! ] ;

! CHR: propagate-dup-right @
! { Dup ?x L{ ?a . ?b } } // -- [ ?x known term-var? ] | [ ?x L{ ?c . ?d } ==! ] ;
! { Dup ?x L{ ?c . ?d } } // -- [ ?x known term-var? ] |
!   { Dup ?a ?c } { Dup ?b ?d } ;

! { Dup L{ ?a . ?b } L{ ?c . ?d } } [ ?x L{ ?a ?b } ==! ] ;
! CHR: propagate-dup-right @
! { Dup ?x ?y } // -- [ ?y known cons-state? ] | [ ?x L{ ?c . ?d } ==! ] ;

! CHR: propagate-dup-left @
! ! { Dup L{ ?a . ?b } ?y } // -- [ ?y atom? ] | [ ?y L{ ?c . ?d } ==! ] ;
! { Dup L{ ?a . ?b } ?y } // -- [ ?y known term-var? ] |
! { Dup ?a ?c } { Dup ?b ?d } ;
! { Dup L{ ?a . ?b } L{ ?c . ?d } } [ ?y L{ ?c ?d } ==! ] ;
! CHR: propagate-dup-left @
! { Dup ?x ?y } // -- [ ?x known cons-state? ] | [ ?y L{ ?c . ?d } ==! ] ;

CHR: destructure-dup @
// { Dup L{ ?a . ?b } L{ ?c . ?d } } -- [ ?b nil? not ] [ ?d nil? not ] | { Dup ?a ?c } { Dup ?b ?d } ;

! ** Forward propagation

! CHR: propagate-drop @ { --> ?c P{ Dead ?y } } { --> ?c P{ is ?x ?y } } // -- | { --> ?c P{ Dead ?x } } ;
! CHR: literal-dup1 @
! { Lit ?x ?v } // { Dup ?x ?y } -- | { Lit ?y ?v } ;

! CHR: literal-dup2 @
! { Lit ?y ?v } // { Dup ?x ?y } -- | { Lit ?x ?v } ;

! ** Backward propagation
! CHR: split-will-be-dead @  { Dead ?y } { Dead ?z } // { Split __ ?x ?y ?z } -- | { Dead ?x } ;
CHR: will-be-dropped @ { EitherOr ?r __ ?c1 ?c2 }
{ --> ?c1 P{ is ?x ?a } } { --> ?c1 P{ Drop ?a } }
{ --> ?c2 P{ is ?x ?b } } { --> ?c2 P{ Drop ?b } } // -- |
{ --> ?r P{ Drop ?x } } ;

! ** Splits and Joins
! *** Simplify
! CHR: redundant-split-1 @ { Absurd ?c1 } { Branch ?r __ ?c1 ?c2 } // { Split ?r ?x ?y ?z } --
! | [ ?x ?z ==! ] ;
! CHR: redundant-split-2 @ { Absurd ?c2 } { Branch ?r __ ?c1 ?c2 } // { Split ?r ?x ?y ?z } --
! | [ ?x ?y ==! ] ;

CHR{ // { Split ?x ?x ?x } -- | }
CHR{ // { Join ?x ?x ?x } -- | }

CHR: non-split @ // { Split ?z ?a ?b } -- [ ?z ?a ?b [ lastcdr ] tri@ [ = ] curry bi@ or ] | ;

! This should happen if branch scopes are inferred to be known and balanced
CHR: redundant-split @ // { Split ?z ?x ?x } -- | [ ?x ?z ==! ] ;
CHR: redundant-join @ // { Join ?z ?x ?x } -- | [ ?x ?z ==! ] ;

TERM-VARS: ?zs ;

CHR: destructure-split @ // { Split L{ ?x . ?xs } L{ ?y . ?ys } L{ ?z . ?zs } } -- |
! { Split ?x ?y ?z }
{ Split ?xs ?ys ?zs } ;

CHR: destructure-split-balance-1 @ // { Split ?x L{ ?y . ?ys } ?rho } -- [ ?rho known term-var? ] |
[ ?rho L{ ?z . ?zs } ==! ]
{ Split ?x L{ ?y . ?ys } ?rho } ;

CHR: destructure-split-balance-2 @ // { Split ?x ?sig L{ ?z . ?zs } } -- [ ?sig known term-var? ] |
[ ?sig L{ ?y . ?ys } ==! ]
{ Split ?x ?sig L{ ?z . ?zs } } ;

CHR: destructure-split-intro-1 @ // { Split ?tau L{ ?y . ?ys } ?z } -- [ ?tau known term-var? ] |
[ ?tau L{ ?x . ?xs } ==! ]
{ Split ?tau L{ ?y . ?ys } ?z } ;

CHR: destructure-split-intro-2 @ // { Split L{ ?x . ?xs } ?sig ?z } -- [ ?sig known term-var? ] |
[ ?sig L{ ?y . ?ys } ==! ]
{ Split L{ ?x . ?xs } ?sig ?z } ;

CHR: split-stack @ // { SplitStack ?x ?y ?z } -- |
! { SameDepth ?x ?y } { SameDepth ?x ?z }
{ Split ?x ?y ?z } ;

CHR: join-stack @ // { JoinStack ?x ?y ?z } -- |
{ Split ?x ?y ?z } ;
! { SameDepth ?x ?y } { SameDepth ?x ?z }
! { Join ?x ?y ?z } ;


CHR: destructure-join @ // { Join L{ ?x . ?xs } L{ ?y . ?ys } L{ ?z . ?zs } } -- |
{ Join ?x ?y ?z }
{ Join ?xs ?ys ?zs } ;

CHR: destructure-same-row @ // { --> ?c P{ is L{ ?x . ?xs } L{ ?y . ?ys } } } -- |
{ --> ?c P{ is ?x ?y } }
{ --> ?c P{ is ?xs ?ys } } ;

CHR: trivial-same-row @ // { --> __ P{ is ?x ?x } } -- | ;


! ** Value info combination
! TODO: this might be useful to make into an interface that different value-level things can answer?

! CHR: phi-val-pred-out-1 @ { Branch ?r __ ?c1 ?c2 } { Join ?r ?x ?a ?b } AS: ?p <={ val-pred ?a . __ } // -- |
! [ ?c1 ?p clone ?x >>value --> boa ] ;

! CHR: phi-val-pred-out-2 @ { Branch ?r __ ?c1 ?c2 } { Join ?r ?x ?a ?b } AS: ?p <={ val-pred ?b . __ } // -- |
! [ ?c2 ?p clone ?x >>value --> boa ] ;

    ;
