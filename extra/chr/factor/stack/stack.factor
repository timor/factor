USING: accessors arrays chr chr.factor chr.factor.types chr.modular chr.parser
chr.state classes combinators combinators.short-circuit effects generic kernel
lists make math math.parser sequences terms types.util ;

IN: chr.factor.stack

! * Basic Stack and Effect assumptions
TUPLE: CompatibleEffects < chr-pred in1 out1 in2 out2 ;
TUPLE: BranchStacks < chr-pred from0 to0 from1 to1 from2 to2 ;
ERROR: imbalanced-branch-stacks i1 o1 i2 o2 ;
TUPLE: Val < chr-pred state var ;
TUPLE: AssumeSameRest < chr-pred l1 l2 ;
TUPLE: StackOp < trans-pred in out ;
M: StackOp state-depends-on-vars
    [
        [ in>> known [ , ] leach* ]
        [ out>> known [ , ] leach* ] bi
    ] { } make ;
TUPLE: StartStack < Stack ; ! marker
TUPLE: EndStack < Stack ; ! marker
! TUPLE: SameEffect < chr-pred in1 out1 in2 out2 ;

: elt-vars ( seq -- seq )
    [ swap dup pair? [ first ] when
      [ nip ] [ number>string "v" prepend ] if*
      uvar
      <term-var>
    ] map-index <reversed> ;

! ** Basic stack handling
CHRAT: basic-stack { CompatibleEffects Stack }

! Convention: If outputs meet, they are set equal.  If an input and an output
! meets, the input absorbs the output.  StackOps have an input and an output.
! Stack declarations are output declarations.  When asking for a stack, a stack
! declaration is consumed.


CHR{ { Stack ?s ?v } // { Stack ?s ?v } -- | }

! CHR: answer-stack @ // { Stack ?s ?rho } { ask { Stack ?s ?x } } -- | [ ?rho ?x ==! ]
! { entailed { Stack ?s ?x } } ;

CHR: same-stack @ { Stack ?s ?v } // { Stack ?s ?w } -- | [ ?v ?w ==! ] ;
! CHR: same-stack @ // { Stack ?s ?v } { Stack ?s ?w } -- | [ ?v ?w ==! ] ;
! CHR: set-stack-defines @ { StartStack ?s ?v } // { Stack ?s ?w } -- | [ ?w ?v ==! ] ;
CHR: define-stack-op-in @ { StackOp ?r __ ?rho __ } // { Stack ?r ?x } -- | [ ?x ?rho ==! ] ;
! CHR: define-stack-op-out @ { StackOp __ ?t __ ?sig } { Stack ?t ?x } // -- | [ ?x ?sig ==! ] ;
CHR: define-stack-op-out @ { StackOp __ ?t __ ?sig } // { Stack ?t ?x } -- | [ ?x ?sig ==! ] ;
! CHR: define-set-stack-op-in @ { StackOp ?r __ ?rho __ } // { StartStack ?r ?x } -- | [ ?x ?rho ==! ] ;
! CHR: define-set-stack-op-out @ { StackOp __ ?t __ ?sig } { StartStack ?t ?x } // -- | [ ?x ?sig ==! ] ;

CHR: define-scope-stack-out @ { Scope __ ?t __ ?sig __ } // { Stack ?t ?x } --
| [ ?x ?sig ==! ] ;


CHR: stack-ops-collide @ { StackOp ?r ?s ?x ?y } // { StackOp ?r ?s ?a ?b }
-- |
[ { ?x ?y } { ?a ?b } ==! ]
! [ "conflict" throw ]
    ;

! CHR: do-stack-op @ { StackOp ?s ?t ?rho ?sig } // -- |
! { Stack ?s ?rho }
! ! { AddLink ?s ?t }
! { Stack ?t ?sig }
!     ;

CHR: compose-stack-op @ // { StackOp ?r ?s ?a ?b } { StackOp ?s ?t ?c ?d } --
| [ ?c ?b ==! ] { StackOp ?r ?t ?a ?d } ;

CHR: answer-stack-op-stack-out @ { StackOp __ ?t __ ?sig } // { ask { Stack ?t ?x } } -- |
[ ?sig ?x ==! ]
{ entailed { Stack ?t ?x } } ;

CHR: answer-stack-op-stack-in @ { StackOp ?r __ ?rho __ } // { ask { Stack ?r ?x } } -- |
[ ?rho ?x ==! ]
{ entailed { Stack ?r ?x } } ;

CHR: answer-stack @ // { Stack ?s ?rho } { ask { Stack ?s ?x } } -- | [ ?rho ?x ==! ]
{ entailed { Stack ?s ?x } } ;
CHR: answer-start-stack @ { StartStack ?s ?rho } // { ask { Stack ?s ?x } } -- | [ ?rho ?x ==! ]
{ entailed { Stack ?s ?x } } ;
CHR: answer-end-stack @ { EndStack ?s ?rho } // { ask { Stack ?s ?x } } -- | [ ?rho ?x ==! ]
{ entailed { Stack ?s ?x } } ;

! From condition system
! CHR{ // { Cond +top+ P{ SameStack ?a ?b } } -- | [ ?a ?b ==! ] }
! CHR{ // { Cond +top+ P{ Same ?x ?y } } -- | [ ?x ?y ==! ] }

! Subroutines for making structure equal
TUPLE: SameDepth < chr-pred stack1 stack2 ;
CHR{ // { SameDepth ?x ?x } -- | }
CHR{ // { SameDepth ?x ?y } -- [ ?x ?y [ known lastcdr ] bi@ = ] | }
CHR{ // { SameDepth L{ ?x . ?xs } L{ ?y . ?ys } } -- | { SameDepth ?xs ?ys } }

CHR: destruc-expand-right @ // { SameDepth L{ ?x . ?xs } ?b } -- [ ?b known term-var? ] |
[ ?b L{ ?y . ?ys } ==! ]
{ SameDepth ?xs ?ys } ;
CHR: destruc-expand-left @ // { SameDepth ?a L{ ?y . ?ys } } -- [ ?a known term-var? ] |
[ ?a L{ ?x . ?xs } ==! ]
{ SameDepth ?xs ?ys } ;

CHR: assume-same-rest @ // { AssumeSameRest ?x ?y } -- [ ?x ?y [ known ] bi@ [ llength* ] same? ] |
! { SameDepth ?x ?y }
[ ?x ?y [ known lastcdr ] bi@ ==! ] ;

: list>simple-type ( list1 -- n last )
    0 swap [ dup atom? ] [ [ 1 + ] dip cdr ] until ; inline

: ?effect-height ( list1 list2 -- n/f )
    [ list>simple-type ] bi@ swapd
    = [ - ] [ 2drop f ] if ;

! Setting up stack branch/merge
CHR: known-effects-balance @ // { ask { CompatibleEffects ?a ?x ?b ?y } } --
[ ?a known ?x known ?effect-height :>> ?v ] [ ?b known ?y known ?effect-height :>> ?w ]
[
    ?v ?w { [ and ] [ = not ] } 2&&
    [ ?a ?x ?b ?y \ imbalanced-branch-stacks boa user-error ] when
    t
] |
{ AssumeSameRest ?a ?b }
{ entailed { CompatibleEffects ?a ?x ?b ?y } } ;

! Default Answer for branch stacks
CHR: assume-balanced-stacks @ // { ask { CompatibleEffects ?a ?x ?b ?y } } -- |
{ AssumeSameRest ?a ?b }
{ AssumeSameRest ?x ?y }
{ entailed { CompatibleEffects ?a ?x ?b ?y } } ;

! CHR: branch-stacks @ { Branch ?r ?u ?s ?t } // -- |
! { Stack ?r ?v } { Stack ?s ?a } { Stack ?t ?b } { Stack ?u ?w }
! { CompatibleEffects ?a ?w }
! { BranchStacks ?a ?b ?c ?d ?e ?w } ;

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
CHR{ // { AssumeWordEffect ?s ?t ?w ?e } -- |
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
     ]
     [ { [ ?w generic? ] [ ?e bivariable-effect? not ] } 0&&
       [ ?rho ?sig ==! ] [ f ] if ]
   }

! CHR: rem-trivial-jump @
! ! { CondJump ?r ?s true } // -- | { Stack ?r ?rho } { Stack ?s ?rho } }
!  // { CondJump ?r ?s true } -- | [ ?r ?s ==! ] ;

! CHR: rem-trivial-ret @
! ! { CondRet ?r ?s true } // -- | { Stack ?r ?rho } { Stack ?s ?rho } }
! // { CondRet ?r ?s true } -- | [ ?r ?s ==! ] ;

CHR: make-push-stack @ // { Push ?s ?t ?b } -- [ ?b known? ] [ P{ Lit ?b } :>> ?x ] |
     ! { Cond ?s { Lit ?v ?b } }
     { StackOp ?s ?t ?rho L{ ?x . ?rho } }
     [ ?x ?b class-of Type boa ]
     ! { Lit ?v ?b }
     ! { Stack ?s ?rho }
     ! { Stack ?t L{ ?v . ?rho } }
    ;

;
