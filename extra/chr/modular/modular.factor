USING: accessors arrays assocs chr classes classes.tuple combinators kernel math
namespaces quotations sequences sets terms vectors words ;

IN: chr.modular

! * Housekeeping
TUPLE: import-solver word ;
C: <import-solver> import-solver

! * Modular Ask and Tell Semantics
! Basic contract for every modular solver:
! leq(X, Y) \ ask(leq(X, Y), K) <=> entailed(K).
! ask(leq(X, X), K) <=> entailed(K).

! FIXME: Useful dependency handling?  Maybe use class methods...
PREDICATE: chrat-pred-class < tuple-class "chrat-solver" word-prop ;
PREDICATE: chrat-solver < word "chrat-deps" word-prop ;
M: chrat-solver reset-word
    [ call-next-method ]
    [ "chrat-deps" remove-word-prop ] bi ;

PREDICATE: chrat-pred < chr-pred constraint-type "chrat-solver" word-prop ;
! PREDICATE: chrat-pred-word < tuple-class "chrat-solver" word-prop ;
! M: chrat-pred-word reset-word
!     [ call-next-method ]
!     [ f "chrat-solver" set-word-prop ] bi ;

! Public
TUPLE: ask < chr-pred pred ;

TUPLE: entailed < chr-pred pred ;

! Private
TUPLE: _ask < chr-pred type vars token ;
C: <_ask> _ask
M: _ask constraint-type [ class-of ] [ type>> ] bi 2array ;

TUPLE: _entailed < chr-pred type vars token ;
C: <_entailed> _entailed
M: _entailed constraint-type [ class-of ] [ type>> ] bi 2array ;

TUPLE: _exists < chr-pred var token ;
C: <_exists> _exists


! Experimental
TUPLE: AskAbout < chr-pred constraint token vars ;
TUPLE: AnswerAbout < chr-pred constraint token vars ;

! env(c...) means variables in the constraints c
! Splitting a rule in the following form into:
! Hk / Hr -- Gb1 Gh1 Gb2 Gh2 | B1 B2 ;
! -> Hk Hr // -- Gb1 | ask(Gh1, k), return(env(Hk+Hr+Gb1+Gh1), r1
! + Hk // Hr, return(env(Hk+Hr+Gb1+Gh1), entailed(k) -- Gb2 Gh2 | B1 B2
! Which in turn is split recursively until no more chr-guards are present
! NOTE: actually not sequencing guards yet!

! NOTE: This assumes that builtins can be exchanged with user-defineds in the guards!
! Actually, the guard check is duplicated.  This is probably wasteful, and the
! builtins should be distributed correctly between call and return rules based
! on position...

PREDICATE: chrat-rule < chr guard>> [ chr-constraint? ] any? ;

GENERIC: rewrite-chrat-conts ( chr -- chrs )
M: chr rewrite-chrat-conts 1array ;

: analyze-chr-guards ( head-vars chr-guards -- asks exists )
    [ "k" utermvar ! head-vars guard token
      [ [ vars swap diff ] dip [ <_exists> ] curry map ]
      [ [ [ constraint-type ]
          [ constraint-args ] bi ] dip
        <_ask> ] 2bi swap 2array
    ] with map unzip concat ;

! Helper
TUPLE: cont-spec head-vars guards asks exists id ;
C: <cont-spec> cont-spec
: cont-spec-term ( cont-spec -- term )
    {
        [ id>> 1vector ]
        [ asks>> [ token>> suffix! ] each ]
        [ head-vars>> append! ]
        [ exists>> [ var>> suffix! ] each ]
    } cleave
    >array ;

:: analyze-cont ( rule -- cont-spec )
    rule guard>> [ chr-constraint? ] partition :> ( chr-guards builtin-guards )
    rule heads>> vars :> head-vars
    head-vars chr-guards analyze-chr-guards :> ( asks exists )
    head-vars builtin-guards asks exists "r" usym <cont-spec> ;

: convert-ask-rule ( rule cont-spec -- rule )
    [ clone ] dip
    {
        [ guards>> >>guard ]
        [ asks>> ]
        ! [ exists>> append ]
        [ cont-spec-term suffix >>body ]
    } cleave
    dup heads>> length >>nkept ;

: ask>entails ( ask-constraint -- entailed-constraint )
    [ type>> ]
    [ vars>> ]
    [ token>> ] tri <_entailed> ;

: convert-fire-rule ( rule cont-spec -- rule )
    [ clone ] dip
    [ guards>> >>guard ]
    [ asks>> [ ask>entails ] map ]
    [ cont-spec-term suffix [ append ] curry change-heads ] tri ;

M: chrat-rule rewrite-chrat-conts
    dup analyze-cont
    [ convert-ask-rule ]
    [ convert-fire-rule ] 2bi 2array ;

: get-ask/entail ( rule -- n-ask n-entail )
    [ heads>> [ ask? ] count ]
    [ body>> [ entailed? ] count ] bi ;

PREDICATE: modular-chr < chr get-ask/entail drop 1 <= ;
PREDICATE: modular-answer-chr < modular-chr get-ask/entail [ 1 = ] both? ;
PREDICATE: invalid-modular-constraint < chr get-ask/entail [ 1 > ] either? ;

GENERIC: expand-ask/tell ( rule -- rule )

! Sends { ask q } to { _ask type vars k }
! and { entailed q } to { _entailed type vars k }
: convert-ask ( token heads -- heads )
    [ dup ask?
      [ pred>> pred>constraint [ constraint-type ] [ constraint-args ] bi rot <_ask> ]
      [ nip ] if
    ] with map ;

: convert-entailed ( token heads -- heads )
    [ dup entailed?
      [ pred>> pred>constraint [ constraint-type ] [ constraint-args ] bi rot <_entailed> ]
      [ nip ] if
    ] with map ;

M: modular-chr expand-ask/tell
    clone __ swap [ convert-ask ] with change-heads ;

M: modular-answer-chr expand-ask/tell
    clone
    "k" uvar <term-var>
    [ swap [ convert-ask ] with change-heads ]
    [ swap [ convert-entailed ] with change-body ] bi ;

M: chr expand-ask/tell ;

GENERIC: rewrite-chrat ( chr -- chr )

M: import-solver rewrite-chrat 1array ;
M: chr rewrite-chrat
    expand-ask/tell
    rewrite-chrat-conts ;

: rewrite-chrat-prog ( rules -- rules )
    [ rewrite-chrat ] map concat ;

: chrat-pred-template ( class -- constraint )
    [ all-slots [ name>> utermvar ] map ]
    [ slots>tuple ] bi ;

: make-default-entailment-rule ( pred -- rule )
    [ name>> "-trivial" append ] keep
    chrat-pred-template
    [ dup ask boa 2array 1 f ]
    [ entailed boa 1array ] bi
    f named-chr new-chr swap >>rule-name ;

! ERROR: redefining-chr-solver solver word ;

: set-defined-solver ( solver word -- )
    swap "chrat-solver" set-word-prop ;
    ! dup "chrat-solver" word-prop
    ! [ redefining-chr-solver ]
    ! [ swap "chrat-solver" set-word-prop ] if ;

GENERIC: pred>chrat-definer ( pred -- rules )

! FIXME: Defining on words/classes here is a mess...
M: chr-pred pred>chrat-definer drop f ;
M: chrat-pred pred>chrat-definer
    constraint-type "chrat-solver" word-prop ;
M: chrat-pred-class pred>chrat-definer
    "chrat-solver" word-prop ;

: chrat-solver-rules ( word -- rules )
    ( -- prog ) execute-effect ;
    ! "constant" word-prop ;

: chrat-solver-deps ( word -- solvers )
    "chrat-deps" word-prop ;


SYMBOL: chrat-imports
: set-chrat-deps ( word -- )
    chrat-imports get [ "chrat-deps" [ append ] with change-word-prop ] [ drop ] if* ;

: define-solver-word ( word prog -- )
    ! 2dup "chr-rules" set-word-prop
    ! 1quotation ( -- prog ) define-declared ;
    [ dup chr? [ [ suffix ] curry ] [ word>> [ execute( -- prog ) append ] curry ] if ] map [ f ] [ compose ] reduce
    ( -- prog ) define-declared ;

: define-chrat-prog ( word exports rules -- )
    2over [ set-defined-solver ] with each
    swap [ make-default-entailment-rule ] map prepend
    [ dup chr? [ internalize-rule ] when ] map
    rewrite-chrat-prog
    define-solver-word ;
    ! [ define-solver-word ] keepd
    ! set-chrat-deps ;
