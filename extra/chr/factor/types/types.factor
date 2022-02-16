USING: chr.factor chr.modular chr.parser classes kernel lists terms ;

IN: chr.factor.types

TERM-VARS: ?s ?v ?x ?xs ?y ?ys ?tau ?k ?vars ;

CHRAT: chrat-types { NotInstance }
CHR{ { Stack ?s ?v } // { AcceptTypes ?s ?x } -- | { AcceptType ?s ?v ?x } }
CHR{ // { AcceptType __ ?v object } -- | }
CHR{ // { AcceptType __ __ L{ } } -- | }
CHR{ // { AcceptType ?s L{ ?x . ?xs } L{ ?y . ?ys } } -- | { AcceptType ?s ?x ?y } { AcceptType ?s ?xs ?ys } }

! TODO: chr-pred inheritance would be nice...
CHR{ { Stack ?s ?v } // { ProvideTypes ?s ?x } -- | { ProvideType ?s ?v ?x } }
CHR{ // { ProvideType __ ?v object } -- | }
CHR{ // { ProvideType __ __ L{ } } -- | }
CHR{ // { ProvideType ?s L{ ?x . ?xs } L{ ?y . ?ys } } -- | { ProvideType ?s ?x ?y } { ProvideType ?s ?xs ?ys } }

CHR{ { Lit ?x ?v } // { AcceptType __ ?x ?tau } -- [ ?v ?tau instance? ] | }
CHR{ { Lit ?x ?v } // { AcceptType ?s ?x ?tau } -- [ ?v ?tau instance? not ] |
     { ConflictState ?s { Lit ?x ?v } { AcceptType ?s ?x ?tau } } }

! CHR: answer-lit-notinstace @ { Lit ?x ?v } // { ask { NotInstance ?x ?tau } } -- [ ?v ?tau instance? not ] |
!      { entailed { NotInstance ?x ?tau } } ;

CHR: answer-lit-instance @ { Lit ?x ?v } { AskAbout { Instance ?x ?tau } ?k ?vars } // -- [ ?v ?tau instance? ] |
{ AnswerAbout { Instance ?x ?tau } ?k ?vars } ;

CHR: answer-no-lit-instance @ { Lit ?x ?v } { AskAbout { Instance ?x ?tau } ?k ?vars } // -- [ ?v ?tau instance? not ] |
{ AnswerAbout { Not { Instance ?x ?tau } } ?k ?vars } ;

;
