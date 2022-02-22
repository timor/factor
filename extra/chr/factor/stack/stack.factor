USING: accessors arrays chr chr.factor chr.factor.conditions
chr.modular chr.parser chr.state combinators combinators.short-circuit kernel
lists math math.parser sequences sets terms ;

IN: chr.factor.stack

! * Basic Stack and Effect assumptions
TUPLE: CompatibleEffects < chr-pred in1 out1 in2 out2 ;
TUPLE: BranchStacks < chr-pred from0 to0 from1 to1 from2 to2 ;
ERROR: imbalanced-branch-stacks i1 o1 i2 o2 ;
TUPLE: Val < chr-pred state var ;
! TUPLE: SameEffect < chr-pred in1 out1 in2 out2 ;

: elt-vars ( seq -- seq )
    [ swap dup pair? [ first ] when
      [ nip ] [ number>string "v" prepend ] if*
      uvar
      <term-var>
    ] map-index <reversed> ;

! ** Basic stack handling
CHRAT: basic-stack { Lit InferredEffect CompatibleEffects }


CHR{ { Stack ?s ?v } // { Stack ?s ?v } -- | }
CHR: same-stack @ { Stack ?s ?v } // { Stack ?s ?w } -- | [ ?v ?w ==! ] ;

! From condition system
! CHR{ // { Cond +top+ P{ SameStack ?a ?b } } -- | [ ?a ?b ==! ] }
! CHR{ // { Cond +top+ P{ Same ?x ?y } } -- | [ ?x ?y ==! ] }

! Setting up stack branch/merge
CHR: check-effects-balance @ // { ask { CompatibleEffects ?a ?x ?b ?y } } --
[ ?a known ?x known ?effect-height :>> ?v ] [ ?b known ?y known ?effect-height :>> ?w ]
[
    ?v ?w { [ and ] [ = not ] } 2&&
    [ ?a ?x ?b ?y \ imbalanced-branch-stacks boa user-error ] when
    t
    ! ?rho lastcdr ?sig lastcdr ==!
] | { entailed { CompatibleEffects ?a ?x ?b ?y } } ;

! Subroutines for making structure equal
TUPLE: SameDepth < chr-pred stack1 stack2 ;
CHR{ // { SameDepth ?x ?x } -- | }
CHR{ // { SameDepth L{ ?x . ?xs } L{ ?y . ?ys } } -- | { SameDepth ?xs ?ys } }

CHR: destruc-expand-right @ // { SameDepth L{ ?x . ?xs } ?b } -- [ ?b known term-var? ] |
[ ?b L{ ?y . ?ys } ==! ]
! [ ?b L{ ?y . ?b } ==! ]
{ SameDepth ?xs ?ys } ;
CHR: destruc-expand-left @ // { SameDepth ?a L{ ?y . ?ys } } -- [ ?a known term-var? ] |
[ ?a L{ ?x . ?xs } ==! ]
! [ ?a L{ ?x . ?a } ==! ]
{ SameDepth ?xs ?ys } ;

! Default Answer for branch stacks
! CHR: assume-balanced-stacks @ { ask { CompatibleEffects ?a ?x ?b ?y } } // -- |
! FIXME: this should be converted automatically!
! CHR: assume-balanced-stacks @ { _ask CompatibleEffects { ?a ?x ?b ?y } __ } // -- |
CHR: assume-balanced-stacks @ // { ask { CompatibleEffects ?a ?x ?b ?y } } -- |
{ SameDepth ?a ?b }
{ SameDepth ?x ?y }
{ entailed { CompatibleEffects ?a ?x ?b ?y } } ;

! CHR: branch-stacks @ { Branch ?r ?u ?s ?t } // -- |
! { Stack ?r ?v } { Stack ?s ?a } { Stack ?t ?b } { Stack ?u ?w }
! { CompatibleEffects ?a ?w }
! { BranchStacks ?a ?b ?c ?d ?e ?w } ;

TERM-VARS: ?zs ;

CHR{ // { Split ?x ?x ?x } -- | }

CHR: destructure-split @ // { Split L{ ?x . ?xs } L{ ?y . ?ys } L{ ?z . ?zs } } -- |
{ Split ?x ?y ?z }
{ Split ?xs ?ys ?zs } ;

CHR{ // { Join ?x ?x ?x } -- | }

CHR: destructure-join @ // { Join L{ ?x . ?xs } L{ ?y . ?ys } L{ ?z . ?zs } } -- |
{ Join ?x ?y ?z }
{ Join ?xs ?ys ?zs } ;
! CHR: assume-split-in @ { Split ?a L{ ?y . __ } __ } // -- [ ?a known term-var? ] |
! [ ?a L{ ?x . ?xs } ==! ] ;
! CHR: assume-split-out-1 @ { Split L{ ?x . __ } ?b __ } // -- [ ?b known term-var? ] |
! [ ?b L{ ?y . ?ys } ==! ] ;
! ! CHR: assume-split-out-2 @ { Split L{ ?x . __ } L{ ?y . __ } ?c } // -- [ ?c known term-var? ] |
! ! [ ?c L{ ?z . ?zs } ==! ] ;
! CHR: balance-split-left @ { Split __ L{ ?y . __ } ?c } // -- [ ?c known term-var? ] |
! [ ?c L{ ?z . ?zs } ==! ] ;
! CHR: balance-split-right @ { Split __ ?b L{ ?z . __ } } // -- [ ?b known term-var? ] |
! [ ?b L{ ?y . ?ys } ==! ] ;



! CHR: same-stack @ // { Stack ?s ?v } { Stack ?s ?w } -- | [ ?v ?w ==! ] ;
CHR: same-effect @ { Effect ?q ?i ?o } // { Effect ?q ?a ?b } -- | [ ?i ?a ==! ] [ ?o ?b ==! ] ;

! CHR{ { Stack ?s ?v } { Val ?s ?n ?a } // -- [ ?n ?v llength* < ] |
!      [ ?a ?n ?v lnth ==! ]
!    }


! This is mainly useful for naming vars according to the declared effects...
CHR{ // { AssumeEffect ?s ?t ?e } -- |
     [| | ?e [ in>> ] [ out>> ] bi 2dup :> ( i o )
      [ length ] bi@ :> ( ni no )
      f
      i elt-vars :> i
      o elt-vars :> o
      ! i [ ?s swap Pops boa suffix ] unless-empty
      ! o [ ?t swap Pushes boa suffix ] unless-empty
      ! i ?s swap Pops boa suffix
      ! o ?t swap Pushes boa suffix

      ! ?s ?t i o In/Out boa suffix


      ! ?s ?t
      ?s i >list ?rho lappend Stack boa suffix
      ! Assume bivariable-effect in general!
      ?t {
           ! { [ ?e terminated?>> ] [ __ ] }
           ! { [ ?e bivariable-effect? ] [ o >list ?sig lappend ] }
           [ o >list ?sig lappend ]
      } cond Stack boa suffix
      ! {
      !     { [ ?e terminated?>> ] [ __ ] }
      !     { [ ?e bivariable-effect? ] [ o >list ?sig lappend ] }
      !     [ o >list ?rho lappend ] } cond InferredEffect boa suffix
     ] }

! CHR: rem-trivial-jump @
! ! { CondJump ?r ?s true } // -- | { Stack ?r ?rho } { Stack ?s ?rho } }
!  // { CondJump ?r ?s true } -- | [ ?r ?s ==! ] ;

! CHR: rem-trivial-ret @
! ! { CondRet ?r ?s true } // -- | { Stack ?r ?rho } { Stack ?s ?rho } }
! // { CondRet ?r ?s true } -- | [ ?r ?s ==! ] ;

CHR: make-push-stack @ // { Push ?s ?t ?b } -- |
     ! { Cond ?s { Lit ?v ?b } }
     { Lit ?v ?b }
     { Stack ?s ?rho }
     { Stack ?t L{ ?v . ?rho } } ;

;
