USING: accessors arrays assocs chr chr.parser classes combinators effects
effects.parser hashtables kernel lexer make namespaces parser persistent.assocs
quotations sequences sequences.generalizations strings types.util vocabs.parser
words ;

IN: chr.factor
FROM: syntax => _ ;

TUPLE: state-pred < chr-pred s1 ;
TUPLE: trans-pred < chr-pred s1 s2 ;

TUPLE: Word < trans-pred word ;

TUPLE: Dispatch < trans-pred cond vset ;
TUPLE: Join < trans-pred cond ;

TUPLE: Not < chr-pred pred ;

TUPLE: Val < state-pred n val ;
TUPLE: Type < state-pred n val ;
TUPLE: Instance < chr-pred val s ;
TUPLE: NotInstance < chr-pred val s ;
TUPLE: ExpectInstance < chr-pred val s ;
TUPLE: DeclareTos < state-pred s ;

TUPLE: Push < trans-pred val ;

TUPLE: AssumeEffect < trans-pred effect ;
TUPLE: InferredEffect < trans-pred in out ;
TUPLE: EitherOr < chr-pred s1 s2 v1 v2 ;

TUPLE: SplitState < state-pred sa sb ;

! Word level
TUPLE: Exec < trans-pred obj ;
TUPLE: ExecWord < trans-pred word ;
TUPLE: Generic < trans-pred word ;
TUPLE: Definition < chr-pred word quot ;
TUPLE: Lit < chr-pred val obj ;
TUPLE: Curried < chr-pred val parm callable ;
TUPLE: Composed < chr-pred val callable1 callable2 ;
TUPLE: CondJump < trans-pred cond ;
TUPLE: CondRet < trans-pred cond ;

! This signifies that the referenced condition is part of an exclusive set?
! TUPLE: Exclusive

! Definition level
TUPLE: InferCall < trans-pred val ;
TUPLE: InlineCall < trans-pred word quot ;
TUPLE: Call < trans-pred word quot ;

! Data Split, duplication
TUPLE: Split < chr-pred from to ;

! Known Stack states
TUPLE: QueryStack < state-pred depth ;
TUPLE: InferredStack < state-pred n vars ;
! TUPLE: BoundedEffect < trans-pred ;

! Boolean if then else, cond is a value, the other two are states
TUPLE: BranchIf < trans-pred cond strue sfalse ;

TUPLE: InferUnknown < trans-pred val ;

: new-state ( -- symbol )
    "s" uvar <term-var> ;

SINGLETON: +top+
! INSTANCE: +top+ match-var
SINGLETON: +end+
! INSTANCE: +end+ match-var

: sub-state ( symbol -- symbol )
    dup +top+? [ drop new-state ] when
    name>> "." append uvar <term-var> ;

: seq-state ( symbol -- symbol )
    dup +top+? [ drop new-state ] when
    name>> uvar <term-var>  ;

SYMBOLS: state-in-var state-out-var ;

: state-in ( -- var )
    state-in-var get [ new-state ] unless* ; inline

: state-out ( -- var )
    state-out-var get [ new-state ] unless* ; inline

: next-state ( -- )
    state-out
    state-in uvar state-out-var set
    state-in-var set ;

! Each call advances the state
: advancing ( quot -- quot )
    [ next-state ] compose ;

: with-states ( si so quot -- )
    '[ _ state-in-var set _ state-out-var set @ ] with-scope ; inline


! : define-word-constraint ( word key effect constraints -- ) ;

! ! : parse-constraints ( effect -- seq ) ;
! : parse-constraints (  )

! TUPLE: row state vals ;
! C: <row> row

! : effect>rows ( effect -- in out )
!     [ in-var>> "si" or ]
!     [ in>>  ]

GENERIC: make-term-var ( elt -- )

M: string make-term-var
    <term-var> dup name>> ,, ;

M: pair make-term-var
    first2 [ make-term-var ]
    [ dup classoid? [ drop ] [ make-term-var ] if ] bi* ;

M: effect make-term-var
    {
        [ in-var>> [ make-term-var ] when* ]
        [ out-var>> [ make-term-var ] when* ]
        [ in>> [ make-term-var ] each ]
        [ out>> [ make-term-var ] each ]
    } cleave ;

: define-term-vars ( effect -- assoc )
    [ make-term-var ] H{ } make ;

! SYMBOL: make-shuffle?
! SYMBOL: state-var
! SYMBOL: position
! GENERIC: make-effect-constraints ( assoc elt -- )
! M: string make-effect-constraints
!     of state-var get swap position get Val boa , ;

! : make-named-type-constraint ( assoc var type -- )
!     [ drop make-effect-constraints ]
!     [ [ of ] dip Instance boa , ] 3bi ;

! : make-anonymous-type-constraint ( assoc var type -- )
!     2nip "v" uvar <term-var>
!     [ state-var get swap position get Val boa , ]
!     [ swap Instance boa , ] bi ;

! : make-type-constraint ( assoc var type -- )
!     make-shuffle? get [ [ drop f ] dip ] unless
!     over [ make-named-type-constraint ]
!     [ make-anonymous-type-constraint ] if ;

! M: pair make-effect-constraints
!     first2
!     {
!         { [ dup classoid? ] [ make-type-constraint ] }
!         { [ dup effect? ] [
!               [ drop callable make-type-constraint ]
!               [ nip make-effect-constraints ] 3bi ] }
!     } cond ;

! M: effect make-effect-constraints ( assoc effect -- )
!     [ dup in-var>> [ pick at ] [ "si" uvar <term-var> ] if*
!       state-var [ in>> <reversed> [ position set swap make-effect-constraints ] with each-index ] with-variable
!     ] [ dup out-var>> [ pick at ] [ "so" uvar <term-var> ] if*
!         state-var [ out>> <reversed> [ position set swap make-effect-constraints ] with each-index ] with-variable
!     ] 2bi ;

! : make-interface-constraints ( effect assoc -- seq )
!     swap [ make-effect-constraints ] { } make ;
!     ! swap effect-interface
!     ! [ make-state-vals ] 2bi@ append ;

! : make-interface-rule ( word effect assoc -- chr )
!     [
!         [ swap in-var>> of ] [ swap out-var>> of ] bi-curry bi
!         rot Word boa 1array f
!     ] [ make-interface-constraints ] 2bi
!     chr new-prop-chr ;


: parse-constraints ( assoc -- seq )
    [ \ ; parse-chr-body ] with-words ;


! * CHR for Factor Code Inference
! : generate-effect-constraints ( effect -- seq )
!     dup define-term-vars make-interface-constraints ;

: set-word-constraints ( word key seq -- )
    spin "chr-constraints" [ [ new-at ] [ associate ] if* ] change-word-prop ;

SYNTAX: CONSTRAINT: scan-word scan-token scan-effect
    define-term-vars
    ! [ make-interface-constraints ]
    ! [ nip parse-constraints ] 2bi
    ! append set-word-constraints
    parse-constraints 3array suffix! ;
    ! [ make-interface-constraints ]
    ! [ nip parse-constraints ] 2bi
    ! append set-word-constraints
    ! ;

SYNTAX: GEN[ scan-effect define-term-vars
            [ values ] keep [ \ ] parse-array ] with-words <generator> suffix! ;


! ! * Inclusion Semantics


! General principle is subset inclusion, which states that a concrete value at
! runtime will be in the set of possible values?
! Also do the negative calculation in parallel ?

! The internal constraints should be as precise as possible.


! E.g. definition:
! : <= ( x y -- b ) ;


! CHR{ { <= x y b } // -- { sub x number } { sub y number } { sub y boolean } }
! CHR{ { <= x y b } // -- { le x y } | [ b f ==! ] }
! CHR{ { <= x y b } // -- { gt x y } | [ b t ==! ] }

! In order to definitively apply a constraint, we need to have proven that either
! the condition value is exactcly not equal to f, or exactly equal to f:
! CHR{ { <= x y b } // -- { ne b f } { sub b object } |  { lt x y } }
! CHR{ { <= x y b } // -- { = b f } | {

! ! Relations of built-in classes

! CHR{ // { sub x boolean } { sub x \ f } -- | [ x f ==! ] }
! CHR{ // { sub x boolean } { sub x t } -- | [ x t ==! ] }
! # CHR{ // { disjoint x y } { sub v y } { sub v x } -- | false }
! # CHR{ { sub x y } // { ask { sub x z } } -- { disjoint x z } | { nosub x z } }
! CHR{ { disjoint x y } { sub v y } // | }
! CHR{ { disjoint x y } { sub v x } // { sub v y } -- | }
! CHR{ { instance x \ f } -- | { sub x boolean } [ x f ==! ] }



! Existential assumptions for booleans, denoting that if there is an exclusive
! choice of control flow, then there are at least two sets which are distinct?
! : if ( cond then else -- ... )
! CHR{ { if c t e } // --
!   { sub t callable } { sub e callable }
!   { split c c1 c2 } { sub c1 s1 } { sub c2 s2 } { disjoint s2 s1 }
!   { dispatch c1 f e }
!   { dispatch c2 s2 t } { ne c2 f }

! * Control inference
! There is a notion of data-dependent jump points, e.g. we need to be able to add certain constraints to
! Data values that will be effective when they get executed.
