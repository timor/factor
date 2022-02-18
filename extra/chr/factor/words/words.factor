USING: assocs chr chr.factor chr.factor.conditions chr.modular chr.parser
chr.state combinators.short-circuit effects generic.single kernel sequences sets
terms words ;

IN: chr.factor.words

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

: chrat-out-types ( word -- seq/f )
    "default-output-classes" word-prop ;

: chrat-methods ( word -- seq/f )
    "methods" word-prop ;

TERM-VARS: ?r ?s ?t ?u ?s0 ?v ?w ?x ?y ?n ?tau ?k ?c ;

CHRAT: chrat-words { DefaultMethod }

CHR{ // { ask { DefaultMethod ?s ?t ?w } } -- [ ?w "default-method" word-prop? ] |
     { entailed { DefaultMethod ?s ?t ?w } } }

CHR{ // { Generic ?s ?t ?w } -- [ ?w single-generic? ] |
     [ ?w [ dispatch# ] [ chrat-methods keys ] bi [| n c | ?s ?t ?w n c SingleMethod boa ] with map ]
   }

! CHR: method-not-applicable @ // { SingleMethod ?s __ __ ?n ?tau } --
!     { Val ?s ?n ?x } { NotInstance ?x ?tau } | ;

! TODO: make this a pattern?
! CHR: ask-method-applicable @ { SingleMethod ?s ?t ?w ?n ?tau } // -- { Val ?s ?n ?x } |
! { AskAbout { Instance ?x ?tau } ?k { ?s ?t ?w ?n ?x ?tau } }
! ;

! This would then be general
! CHR: excluded-middle-1 @ { AnswerAbout { Not ?c } __ ?k } // { AskAbout ?c __ ?k } -- | ;
! CHR: excluded-middle-2 @ { AnswerAbout ?c __ ?k } // { AskAbout { Not ?c } __ ?k } -- | ;

CHR: method-applicable @
{ SingleMethod ?s ?t ?w ?n ?tau }
//
{ AskAbout __ ?k __ }
{ AnswerAbout { Instance ?x ?tau } ?k { ?s ?t ?w ?n ?x ?tau } } -- | ;

CHR: method-not-applicable @
// { SingleMethod ?s ?t ?w ?n ?tau }
{ AskAbout __ ?k __ }
{ AnswerAbout { Not { Instance ?x ?tau } } ?k { ?s ?t ?w ?n ?x ?tau } } -- | ;

! ** Dispatch
CHR{ // { SingleMethod ?s ?u ?w ?n ?tau } -- | { Val ?s ?n ?x }
    [| |
     ?tau ?w chrat-methods at :> method
     {
         { CondJump ?s ?s0 }
         { AcceptType ?s0 ?x ?tau }
         { Cond ?c { Instance ?x ?tau } }
         { ExecWord ?s0 ?t method }
         { CondRet ?t ?u ?s0 }
     }
    ] }

! * Create Rules for instantiation
TUPLE: CompileRule < chr-pred ;
TUPLE: CompileDone < chr-pred ;
! ** Cleanup

! Erase inner state-specific info, so we can treat stacks as conditions
! CHR{ { CompileRule } // { Entry ?s ?w } -- [ ?s ?ground-value +top+ = ] | { TopEntry +top+ ?w } }
CHR{ { CompileRule } // { Entry ?s ?w } -- [ ?s +top+? not ] | { Cond ?s P{ Inlined ?w } } }
! CHR{ { CompileRule } // { Stack ?s __ } -- [ ?s { +top+ +end+ } in? not ] | }
CHR{ { CompileRule } // { Val __ __ __ } -- | }
! CHR{ { CompileRule } // { FoldQuot __ __ __ __ } -- | }
! CHR{ { CompileRule } // { LitStack __ __ __  } -- | }
! CHR{ { CompileRule } // { AskLit __ __ __  } -- | }
CHR{ { CompileRule } // { CondRet __ __ __  } -- | }
CHR{ { CompileRule } // { Dead __ } -- | }
CHR{ { CompileRule } // { Lit ?x __ } { Instance ?x __ } -- | }
! CHR{ { CompileRule } // { InlineUnknown ?s ?t ?x } -- | { Cond ?s { InlinesUnknown ?x } } }
CHR: remove-words-1 @ { CompileRule } // { Generic __ __ __ } -- | ;
CHR: remove-words-2 @ { CompileRule } // { Word __ __ __ } -- | ;

! Wrap some state-specific Conds
CHR: wrap-facts-1 @ { CompileRule } // { AcceptType ?s ?x ?tau } -- | { Cond ?s P{ AcceptType ?s ?x ?tau } } ;
CHR: wrap-facts-2 @ { CompileRule } // { ProvideType ?s ?x ?tau } -- | { Cond ?s P{ ProvideType ?s ?x ?tau } } ;

! CHR: rewrite-conds @ { CompileRule } { Linkback ?s ?v } // { AcceptType ?t ?x ?tau } -- [ ?t ?v known in? ] | { AcceptType ?s ?x ?tau } ;
! CHR: rewrite-conflicts @ { CompileRule } { Linkback ?s ?v } // { ConflictState ?t ?c ?k } -- [ ?t ?v known in? ] | { ConflictState ?s ?c ?k } ;

! CHR: jump-state-is-cond @ { CompileRule } // { CondJump ?r ?s ?t } -- | [ ?s ?t ==! ] { CondNest ?r ?s } ;

! Collapse states
! CHR: collapse-links @ { CompileRule } // { Linkback ?s ?v } -- | [ ?s ?v members [ ==! ] with map ] ;
! CHR: leader-is-cond-1 @ { CompileRule } { Linkback ?s ?v } // { Cond ?x ?c } -- [ ?x ?v known in? ] | { Cond ?s ?c }  ;
! CHR: leader-is-cond-2 @ { CompileRule } { Linkback ?s ?v } // { CondNest ?x ?y } -- [ ?x ?v known in? ] | { CondNest ?s ?y }  ;

! CHR: leader-is-cond @ { CompileRule } { Linkback ?s ?v } // { CondNest ?x ?y } -- [ ?x ?v known in? ] | [ ?s ?x ==! ] ;

CHR{ { CompileRule } { Absurd ?x } { CondNest ?x ?s } // -- | { Absurd ?s } }
CHR{ { CompileRule } { Absurd ?x } // { CondNest __ ?x } -- | }



! CHR: trivial-is-true @ { Trivial ?y } { CondNest ?x ?y } // { Cond ?y ?c } -- | { Cond ?x ?c } ;
CHR: trivial-is-true @ { CompileRule } { CondNest ?x ?y } // { Trivial ?y } -- |  [ ?x ?y ==! ] ;

! Erase Simplification artefacts
! CHR{ { CompileRule } // { Linkback __ __ } -- | }

CHR{ // { CompileRule } -- | { CompileDone } }

CHR{ { CompileDone } // { Absurd __ } -- | }

CHR{ // { CompileDone } -- | }
;
