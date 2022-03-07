USING: chr chr.factor chr.factor.conditions chr.factor.types chr.parser
chr.state kernel sequences sets terms types.util ;

IN: chr.factor.dead-code

! ** GC
TUPLE: Mark < chr-pred vals ;
TUPLE: Marked < chr-pred pred ;
TUPLE: StartGC < chr-pred ;
TUPLE: Sweep < chr-pred ;
TUPLE: SweepDone < chr-pred ;

CHRAT: dead-code { StartGC }
! CHR: start-gc @ { CompileDone } // -- [ V{ +top+ +end+ } clone :>> ?a ] | { Mark ?a } ;
! CHR: gc-after-compile @ { CompileDone } // -- | { StartGC } ;
! CHR: complete-depth-relation-1 @ { StartGC } { SameDepth ?x ?y } { SameDepth ?y ?z } // -- | { SameDepth ?x ?z } ;
! CHR: complete-depth-relation-2 @ { StartGC } { SameDepth ?y ?x } { SameDepth ?y ?z } // -- | { SameDepth ?x ?z } ;
CHR: start-gc @ // { StartGC } -- [ V{ +top+ +end+ } clone :>> ?a ] | { Mark ?a } ;

CHR: mark-effects @ // AS: ?p <={ Effect ?q ?r ?u } { Mark ?a } -- [ ?q ?a in? ] | { Marked ?p } [ ?a ?r suffix! ?u suffix! Mark boa ] ;
CHR: mark-stack-vals @ // AS: ?p <={ Stack ?x ?i } { Mark ?a } -- [ ?x ?a in? ] | { Marked ?p } [ ?a ?i [ [ suffix! ] leach* ] [ lastcdr suffix! ] bi Mark boa ] ;
CHR: mark-xor @ // AS: ?p <={ EitherOr ?x __ ?c1 ?c2 } { Mark ?a } -- [ ?x ?a in? ] | { Marked ?p } [ ?a ?c1 suffix! ?c2 suffix! Mark boa ] ;
CHR: mark-inlining @ // AS: ?p <={ InlinesUnknown ?c ?q } { Mark ?a } -- [ ?c ?a in? ] | { Marked ?p } [ ?a ?q suffix! Mark boa ] ;
! CHR: mark-depth-relations @ // AS: ?p <={ SameDepth ?x ?y } { Mark ?a } -- [ ?x ?a in? ?y ?a in? or ] | { Marked ?p } [ ?a ?y suffix! ?x suffix! members Mark boa ] ;
! TODO: ask for live-deps!
CHR: mark-type-deps @ // AS: ?p <={ type-pred ?x . ?tau } { Mark ?a } -- [ ?x ?a in? ] | { Marked ?p } [ ?a ?tau term-vars members [ suffix! ] each Mark boa ] ;
! CHR: mark-test-preds @ { Mark ?a } // AS: ?p <={ test-pred ?x . __ } -- [ ?x ?a in? ] | { Marked ?p } ;
CHR: mark-test-preds @ // { Mark ?a } AS: ?p <={ test-pred ?x . ?r } -- [ ?x ?a in? ] | { Marked ?p } [ ?a ?r term-vars members [ suffix! ] each members Mark boa ] ;
! CHR: mark-not-preds @ { Mark ?a } // AS: ?p <={ Not ?p } -- [ ?p constraint-args first ?a in? ] | { Marked ?p } ;
CHR: mark-not-preds @ // { Mark ?a } AS: ?p <={ Not ?q } -- [ ?q constraint-args first ?a in? ] | { Marked ?p } { Mark ?a } ;
CHR: mark-impl-preds @ // AS: ?p <={ impl-pred ?x . ?r } { Mark ?a } -- [ ?r term-vars [ ?a in? ] any? ] | { Marked ?p } [ ?a ?x term-vars members [ suffix! ] each Mark boa ] ;

CHR: mark-done @ // { Mark __ } -- | { Sweep } ;

CHR: sweep-test-preds @ { Sweep } // AS: ?p <={ test-pred } -- | ;
CHR: sweep-cond-preds @ { Sweep } // AS: ?p <={ cond-pred } -- | ;
CHR: sweep-state-preds @ { Sweep } // AS: ?p <={ state-pred } -- | ;
CHR: sweep-not-preds @ { Sweep } // { Not __ } -- | ;
! CHR: sweep-rel-preds @ { Sweep } // { SameDepth __ __ } -- | ;
CHR: sweep-done @ // { Sweep } -- | { SweepDone } ;

CHR: sweep @ { SweepDone } // { Marked ?p } -- | [ ?p known ] ;

CHR: end-gc @ // { SweepDone } -- | ;

;

! Only keep top conditions!
! CHR: only-top-conds @ { CompileDone } // SUB: ?x cond-pred L{ ?c . __ } -- [ ?c known +top+? not ] | ;
