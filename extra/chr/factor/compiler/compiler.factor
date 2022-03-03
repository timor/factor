USING: accessors assocs chr chr.comparisons chr.factor chr.factor.conditions
chr.factor.types chr.parser chr.state kernel match namespaces sequences sets
sets.extras terms types.util words ;

IN: chr.factor.compiler

FROM: syntax => _ ;
FROM: namespaces => set ;

! * Compiler interface for chrat-based Interference of Factor code

! ** Create Rules for instantiation
TUPLE: CompileRule < chr-pred ;
TUPLE: CompileDone < chr-pred ;
TUPLE: InferMode < chr-pred ;
TUPLE: Mark < chr-pred vals ;
TUPLE: Marked < chr-pred pred ;

! * Factor Side and Interface
: constraints>body ( store -- constraint )
    ! Make sure we convert the body vars in a fresh scope
    f defined-equalities-ds [ values rest fresh [ term-vars ] keep <generator> ] with-global-variable ;

SYMBOL: rules-cache
SYMBOL: inline-history
: with-jit-compile ( quot -- )
    [ H{ } clone rules-cache set
      V{ } clone inline-history set ] prepose with-scope ; inline

ERROR: recursive-chrat-compile word ;
: (chrat-compile) ( quot/word -- constraints )
    dup inline-history get in? [ recursive-chrat-compile ] when
    inline-history [ over suffix ] change
    '{ { ChratInfer _ } { CompileRule } } run-chrat-query
    constraints>body ;

: chrat-compile-def ( word -- )
    dup "chrat-rules" remove-word-prop
    dup (chrat-compile) "chrat-rules" set-word-prop ;

: chrat-word-rules ( word -- constraint )
    ! "chrat-rules" word-prop ;
    rules-cache get [
        f defined-equalities-ds [ (chrat-compile) ] with-global-variable
    ] cache ;
    ! dup "chrat-rules" word-prop [ nip ]
    ! [ dup (chrat-compile) [ "chrat-rules" set-word-prop ] ]

: instantiate-scope ( generator assoc -- generator )
    [ replace-partial? on replace-patterns ] with-variables ;

:: instantiate-word-rules ( r s w -- new )
    ! "haha" .
    ! defined-equalities .
    w chrat-word-rules
    ! w "chrat-rules" word-prop
    ! "foo" .
    ! defined-equalities .
    [ dup vars>>
      import-vars
      ! drop
      H{ { +top+ r } { +end+ s } } instantiate-scope ] [ f ] if* ;
    ! valid-match-vars [ lift ] with-variable-off ;

: chrat-compile ( quot/word -- constraints )
    [ (chrat-compile) ] with-jit-compile ;

: chrat-infer ( quot/word -- constraints )
    [ '{ { ChratInfer _ } } run-chrat-query ] with-jit-compile ;

! * Chrat side


CHRAT: compile-rules { }

CHR: infer-done @ { CompileRule } // { InferMode } -- | ;

CHR: query-types @ { CompileRule } { Scope +top+ +end+ ?rho ?sig __ } // -- |
[ ?rho list>array* ?sig list>array* symmetric-diff
 [ "tau" uvar <term-var> Type boa ] map ] ;

CHR: define-top-stacks @ { CompileRule } // { Scope +top+ +end+ ?rho ?sig __ } -- | { Stack +top+ ?rho } { Stack +end+ ?sig } ;

CHR: assign-atomic-container-types @ { CompileRule } // { Type ?x ?tau } { Subtype ?tau A{ ?sig } } -- | { Type ?x ?sig } ;

! NOTE: We can treat these literals as dead if we don't care about the call.
! CHR: partial-fold-lits-are-dead @ { CompileRule } { FoldCall __ __ ?i __ } // { --> __ P{ is ?x A{ ?v } } } -- [ ?x ?i known in? ] | ;
! CHR: partial-fold-lits-are-dead @ { CompileRule } <={ Call __ __ ?i . __ } { is ?x A{ ?v } } // -- [ ?x ?i known in? ] | { Dead ?x } ;

! CHR: assume-top-again @ { CompileRule } // AS: ?p <={ val-pred __ . __ } -- [ ?p Dead? not ] | { --> +top+ ?p } ;

! CHR: rm-states @ { CompileRule } // <={ state-pred ?s . __ } -- [ ?s +top+ = not ] [ ?s +end+ = not ] | ;

! *** Erase Simplification artifacts

! CHR{ { CompileRule } // { Dead __ } -- | }
! CHR{ { CompileRule } // { AskLit __ __ } -- | }

CHR{ // { CompileRule } -- | { CompileDone } }

! CHR{ { CompileDone } // { Dead __ } -- | }
! ** GC
TUPLE: StartGC < chr-pred ;
TUPLE: Sweep < chr-pred ;
TUPLE: SweepDone < chr-pred ;

! CHR: start-gc @ { CompileDone } // -- [ V{ +top+ +end+ } clone :>> ?a ] | { Mark ?a } ;
CHR: gc-after-compile @ { CompileDone } // -- | { StartGC } ;
! CHR: complete-depth-relation-1 @ { StartGC } { SameDepth ?x ?y } { SameDepth ?y ?z } // -- | { SameDepth ?x ?z } ;
! CHR: complete-depth-relation-2 @ { StartGC } { SameDepth ?y ?x } { SameDepth ?y ?z } // -- | { SameDepth ?x ?z } ;
CHR: start-gc @ // { StartGC } -- [ V{ +top+ +end+ } clone :>> ?a ] | { Mark ?a } ;

CHR: mark-effects @ // AS: ?p <={ Effect ?q ?r ?u } { Mark ?a } -- [ ?q ?a in? ] | { Marked ?p } [ ?a ?r suffix! ?u suffix! Mark boa ] ;
CHR: mark-stack-vals @ // AS: ?p <={ Stack ?x ?i } { Mark ?a } -- [ ?x ?a in? ] | { Marked ?p } [ ?a ?i [ suffix! ] leach* Mark boa ] ;
CHR: mark-xor @ // AS: ?p <={ EitherOr ?x ?c1 ?c2 } { Mark ?a } -- [ ?x ?a in? ] | { Marked ?p } [ ?a ?c1 suffix! ?c2 suffix! Mark boa ] ;
CHR: mark-inlining @ // AS: ?p <={ InlinesUnknown ?c ?q } { Mark ?a } -- [ ?c ?a in? ] | { Marked ?p } [ ?a ?q suffix! Mark boa ] ;
! CHR: mark-depth-relations @ // AS: ?p <={ SameDepth ?x ?y } { Mark ?a } -- [ ?x ?a in? ?y ?a in? or ] | { Marked ?p } [ ?a ?y suffix! ?x suffix! members Mark boa ] ;
! TODO: ask for live-deps!
CHR: mark-subtype-deps @ { Subtype ?x ?tau } // { Mark ?a } -- [ ?x ?a in? ] | [ ?a ?tau term-vars [ suffix! ] each Mark boa ] ;
! CHR: mark-test-preds @ { Mark ?a } // AS: ?p <={ test-pred ?x . __ } -- [ ?x ?a in? ] | { Marked ?p } ;
CHR: mark-test-preds @ // { Mark ?a } AS: ?p <={ test-pred ?x . __ } -- [ ?x ?a in? ] | { Marked ?p } { Mark ?a } ;
! CHR: mark-not-preds @ { Mark ?a } // AS: ?p <={ Not ?p } -- [ ?p constraint-args first ?a in? ] | { Marked ?p } ;
CHR: mark-not-preds @ // { Mark ?a } AS: ?p <={ Not ?q } -- [ ?q constraint-args first ?a in? ] | { Marked ?p } { Mark ?a } ;
CHR: mark-impl-preds @ // AS: ?p <={ impl-pred ?x . ?r } { Mark ?a } -- [ ?r term-vars [ ?a in? ] any? ] | { Marked ?p } [ ?a ?x suffix! Mark boa ] ;

CHR: mark-done @ // { Mark __ } -- | { Sweep } ;

CHR: sweep-test-preds @ { Sweep } // AS: ?p <={ test-pred } -- | ;
CHR: sweep-cond-preds @ { Sweep } // AS: ?p <={ cond-pred } -- | ;
CHR: sweep-state-preds @ { Sweep } // AS: ?p <={ state-pred } -- | ;
CHR: sweep-not-preds @ { Sweep } // { Not __ } -- | ;
! CHR: sweep-rel-preds @ { Sweep } // { SameDepth __ __ } -- | ;
CHR: sweep-done @ // { Sweep } -- | { SweepDone } ;

CHR: sweep @ { SweepDone } // { Marked ?p } -- | [ ?p known ] ;

CHR: end-gc @ // { SweepDone } -- | ;

! Only keep top conditions!
! CHR: only-top-conds @ { CompileDone } // SUB: ?x cond-pred L{ ?c . __ } -- [ ?c known +top+? not ] | ;

CHR{ // { CompileDone } -- | }
;
