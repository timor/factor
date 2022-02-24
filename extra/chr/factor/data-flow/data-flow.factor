USING: chr.factor chr.factor.conditions chr.modular chr.parser chr.state kernel
lists terms ;

IN: chr.factor.data-flow

! ** Data Flow
CHRAT: data-flow { Effect Copy Split Dup }

! Remove dropped literals
CHR{ // { Drop ?x } { Lit ?x __  } -- | { Dead ?x } }

! *** Sanity checks
CHR{ { Drop ?x } { Drop ?x } // -- | [ "double drop" throw ] }
CHR{ { Dup ?x ?y } { Dup ?x ?y } // -- | [ "douple dup" throw ] }
! CHR{ { Dup ?x ?y } // { Dup ?x ?y } -- | }
CHR{ { Dup ?x ?x } // -- | [ "self-dup" throw ] }

CHR{ // { Dup ?x ?y } { Drop ?y } -- | [ ?x ?y ==! ] }
CHR{ // { Dup ?x ?y } { Drop ?x } -- | [ ?x ?y ==! ] }

CHR{ { Dup ?x ?y } // { ask { Copy ?x ?y } } -- | { entailed { Copy ?x ?y } } }
CHR{ { Split __ ?a ?x ?y } // { ask { Copy ?a ?y } } -- | { entailed { Copy ?a ?y } } }
CHR{ { Split __ ?a ?x ?y } // { ask { Copy ?a ?x } } -- | { entailed { Copy ?a ?y } } }
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

CHR: make-dup-right @ { Dup L{ ?a . ?b } ?y } // -- [ ?y known term-var? ] |
{ Dup L{ ?a . ?b } L{ ?c . ?d } } [ ?y L{ ?c . ?d } ==! ] ;

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

CHR: literal-dup1 @
{ Lit ?x ?v } // { Dup ?x ?y } -- | { Lit ?y ?v } ;

CHR: literal-dup2 @
{ Lit ?y ?v } // { Dup ?x ?y } -- | { Lit ?x ?v } ;

! ** Backward propagation
CHR: split-will-be-dead @  { Dead ?y } { Dead ?z } // { Split __ ?x ?y ?z } -- | { Dead ?x } ;

! ** Splits and Joins

CHR: pushdown-literals @ { Split __ ?x ?y ?z } // { Lit ?x ?v } -- | { Lit ?y ?v } { Lit ?z ?v } ;

TERM-VARS: ?zs ;

CHR{ // { Split __ ?x ?x ?x } -- | }

CHR: destructure-split @ // { Split ?s L{ ?x . ?xs } L{ ?y . ?ys } L{ ?z . ?zs } } -- |
{ Split ?s ?x ?y ?z }
{ Split ?s ?xs ?ys ?zs } ;

CHR{ // { Join __ ?x ?x ?x } -- | }

CHR: destructure-join @ // { Join ?s L{ ?x . ?xs } L{ ?y . ?ys } L{ ?z . ?zs } } -- |
{ Join ?s ?x ?y ?z }
{ Join ?s ?xs ?ys ?zs } ;

! ** Value info combination
! TODO: this might be useful to make into an interface that different value-level things can answer?
;
