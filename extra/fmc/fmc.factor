USING: accessors arrays assocs classes combinators combinators.short-circuit
compiler.tree.debugger effects kernel lists math namespaces quotations sequences
sets strings typed types.util variants words ;

IN: fmc

! * Willem Heijltjes Functional Machine Calculus

! Two ways of representing: ordered list of term-parts, or tree of binary terms

! Evaluated location specifier: word or string
TUPLE: varname { name string } ;
C: <varname> varname
TUPLE: fmc-prim obj ;
C: <fmc-prim> fmc-prim
TUPLE: prim-call word out-names ;
C: <prim-call> prim-call
TUPLE: loc-push body { loc maybe{ word } } ;
C: <loc-push> loc-push
TUPLE: loc-pop { var maybe{ varname } } { loc maybe{ word } } ;
C: <loc-pop> loc-pop
UNION: loc-op loc-push loc-pop ;

SINGLETON: +retain+
SINGLETON: +omega+
SINGLETON: +tau+
SINGLETON: +psi+
UNION: fmc-seq-term ! fmc-term
    varname fmc-prim prim-call loc-push loc-pop ;
: fmc-sequence? ( seq -- ? )
    [ dup sequence? [ fmc-sequence? ] [ fmc-seq-term? ] if ] all? ;
PREDICATE: fmc-seq < sequence fmc-sequence? ;
TUPLE: fmc-cons < cons-state ;
C: <fmc-cons> fmc-cons
M: \ fmc-cons swons*
    drop swap fmc-cons boa ;
UNION: fmc-atom fmc-seq-term ;

UNION: proper-fmc-cdr +nil+ fmc-cons ;
: (proper-fmc-list?) ( obj -- ? )
    dup fmc-cons?
    [ uncons [ { [ fmc-atom? ] [ (proper-fmc-list?) ] } 1|| ] [ proper-fmc-cdr? ] bi* and ]
    [ drop f ] if
    ;
PREDICATE: proper-fmc-list < fmc-cons (proper-fmc-list?) ;

UNION: fmc-term +nil+ proper-fmc-list ;
PREDICATE: fmc-var < fmc-cons car varname? ;
TYPED: <fmc-var> ( cont: fmc-term var: varname -- term: fmc-var ) fmc-cons swons* ;
PREDICATE: fmc-appl < fmc-cons car loc-push? ;
TYPED: <fmc-appl> ( cont: fmc-term push: loc-push -- term: fmc-appl ) fmc-cons swons* ;
PREDICATE: fmc-abs < fmc-cons car loc-pop? ;
TYPED: <fmc-abs> ( cont: fmc-term pop: loc-pop -- term: fmc-abs ) fmc-cons swons* ;
PREDICATE: fmc-const < fmc-cons car fmc-prim? ;
TYPED: <fmc-const> ( cont: fmc-term obj: fmc-prim -- term: fmc-const ) fmc-cons swons* ;

UNION: fmc fmc-seq-term fmc-term ;

GENERIC: >fmc* ( object -- term: fmc-seq )
TYPED: <const> ( obj -- e: fmc-seq ) <fmc-prim> 1array ;
M: object >fmc*
    [ <const> +psi+ <loc-push> ]
    [ class-of <const> +tau+ <loc-push> ] bi 2array ;


DEFER: seq>proper
M: quotation >fmc* [ >fmc* ] map concat ! seq>proper f <loc-push>
    ! f <loc-push>
    1array ;
PREDICATE: shuffle-word < word "shuffle" word-prop ;

SYMBOL: word-stack

TYPED: word-intro ( word -- term: fmc-seq )
    stack-effect effect-in-names
    [ "i" or uvar <varname> ] map
    [ [ f <loc-pop> ] map ]
    [ <reversed> [ f <loc-push> ] map ] bi append ;

! TYPED: word-inst ( body word --  term: fmc )
!     name>> uvar f loc-pop 1quotation

! TODO: recursive
! TYPED: recursive>fmc ( word -- term: fmc )

TYPED: exec>fmc ( word -- term: fmc-seq )
    [ word-intro ]
    [ def>> >fmc* first ] bi append ;
    ! def>> >fmc* first ;

TYPED: shuffle>fmc ( word -- term: fmc-seq )
    "shuffle" word-prop
    [ in>> ] [ out>> ] bi uvar-shuffle
    [ [ <varname> ] map ] bi@
    [ [ f <loc-pop> ] map ]
    [ <reversed> [ f <loc-push> ] map ] bi* append ;

ERROR: recursive-fmc word ;

! : out-locs ( effect -- out-locs )
!     effect-out-names [ "o" or uvar ] map ;

: access-vars ( word -- in-vars out-vars )
    stack-effect
    [ effect-in-names [ "i" or uvar <varname> ] map ]
    [ effect-out-names [ "o" or uvar <varname> ] map ] bi ;

TYPED: lazy-call ( word in-vars out-vars -- term: fmc-seq )
    [ <const> ]
    [ append  ]
    [ append ] tri* ;

! ! Template: foo  ... ⟨i1⟩ ⟨i2⟩ [ i1 i2 + o1 o2 ] [ o1 ] [ o2 ] ...
! TYPED: prim-call>fmc ( word -- term: fmc-seq )
!     dup
!     access-vars
!     [ lazy-call 1array ] 2keep
!     [ [ f <loc-pop> ] map prepend ]
!     [ [ f <loc-push> ] map append ] bi* ;
!     ! [ <const> ]
!     ! stack-effect effect-out-names [ "o" or uvar <varname> ] map ;

! Alternative: return through locs?
! [ fixnum+ ] → [ [ fixnum+ ] call ] → [ [ fixnum+ ] ⟨x⟩ x ]
! ! → [ fixnum+ ⟨x⟩ c⟨_⟩ [x]c [ c⟨y⟩ [y]c [y] ] ]
! → [ fixnum+ ⟨x⟩ c⟨_⟩ [x]c [ c⟨y⟩ [y]c [y] ] ]
! → [ ⟨b⟩ ⟨a⟩ [ a b fixnum+ ⟨x⟩ c⟨_⟩ [x]c ]emit c⟨y⟩ [y]c [y] ]

! Alternative: insert inference markers?
! [ [ + ] [ - ] if ]


TYPED: call-preamble ( in-vars out-vars -- term: fmc-seq )
    ! [ [ f <loc-pop> ] map ]
    ! [ [ +omega+ <loc-pop> ] map ] bi* append ;
    drop [ f <loc-pop> ] map ;

TYPED: call-postamble ( in-vars out-vars -- term: fmc-seq )
    nip
    [ <reversed> [ +omega+ <loc-pop> ] map ]
    [ [ f <loc-push> ] map ] bi append ;
    ! nip
    ! [ f <loc-push> ] map ;

TYPED: call-expr ( word in-vars out-vars -- term: fmc-seq )
    drop
    [ <const> ] dip append 1array 1array ;

! Template: foo  ... λ⟨i1⟩ λ⟨i2⟩ foo ω⟨o1⟩ ω⟨o2⟩ [o1]λ [o2]λ ...
! Could implement folding on omega stack?
TYPED: prim-call>fmc ( word -- term: fmc-seq )
    dup access-vars
    ! [ call-expr ] 2keep
    [ <const> ] 2dip
    ! [ <const> ] [ access-vars ] bi
    [ call-preamble prepend ]
    [ call-postamble append ] 2bi ;

! TYPED: prim-call>fmc ( word -- term: fmc-seq )
!     ! [ word-intro ]
!     ! [ dup stack-effect effect-out-names [ "o" or uvar ] map ] bi
!     ! [ <prim-call> suffix ] keep [ <varname> ] map append ;
!     [ stack-effect in>> length [ curry ] n*quot >quotation >fmc* first ]
!     [ <const> ] bi prefix ;


TYPED: word>fmc ( word -- term: fmc-seq )
    dup word-stack get in? [ recursive-fmc ] when
    { { [ dup shuffle-word? ] [ shuffle>fmc ] }
      { [ dup primitive? ] [ <const> ] }
      ! { [ dup primitive? ] [ prim-call>fmc ] }
      ! { [ dup { call } in? ] [ <const> ] }
      [ word-stack get over suffix word-stack
        [ exec>fmc ] with-variable ]
    } cond ;

M: word >fmc*
    word>fmc ;

! * Special primitives

M: \ dip >fmc* drop
    [ swap >R call R> ] >fmc* first ;

M: \ >R >fmc* drop
    "v" uvar <varname>
    [ f <loc-pop> ]
    [ +retain+ <loc-push> ] bi 2array ;

M: \ R> >fmc* drop
    "v" uvar <varname>
    [ +retain+ <loc-pop> ]
    [ f <loc-push> ] bi 2array ;

M: \ call >fmc* drop
    "q" uvar <varname>
    [ f <loc-pop> ]
    [ +psi+ <loc-push> ] bi 2array ;

! Takes two args from the stack
! Top-most is a callable
! Below that is an object
! When called: 1. push object
! 2. Call callable
M: \ curry >fmc* drop
    [let
     "p" uvar <varname> :> o
     "c" uvar <varname> :> c
     c f <loc-pop>
     o f <loc-pop>
     o f <loc-push>
     c 2array 3array
    ] ;

M: \ compose >fmc* drop
    "ca" uvar <varname>
    "cb" uvar <varname>
    [ swap [ f <loc-pop> ] bi@ ] 2keep
    2array 3array ;

! * Term operations

! Compose N;M -> (N.M)
DEFER: (subst-fmc)
TYPED: <fresh> ( n: varname -- n': varname )
    name>> uvar <varname> ;
TYPED: fresh-pop ( pop: loc-pop -- pop': loc-pop )
    loc-pop unboa [ <fresh> ] dip loc-pop boa ;
TYPED: fresh-pop-subst ( pop: loc-pop -- old: varname fresh: varname pop': loc-pop )
    dup fresh-pop
    [ [ var>> ] bi@ swap ] keep ;

TYPED: (compose-fmc) ( m: fmc-term n: fmc-term -- n.m: fmc-term )
    [ ]
    {
        { +nil+ [ drop (compose-fmc) ] }
        { varname [ [ (compose-fmc) ] dip <fmc-var> ] }
        { fmc-prim [ [ (compose-fmc) ] dip <fmc-const> ] }
        { loc-push [ [ (compose-fmc) ] dip <fmc-appl> ] }
        { loc-pop [ fresh-pop-subst [ rot (subst-fmc) (compose-fmc) ] dip <fmc-abs> ] }
    } lmatch ;

! If we carry over a var-name, then it is composed as a single fmc-var
TYPED: ensure-fmc-term ( m: fmc -- m': fmc-term )
    dup varname? [ +nil+ swap <fmc-var> ] when ;

! Substitute M for x in N
TYPED:: (subst-fmc) ( m: union{ fmc-term varname } v: varname n: fmc -- m/xn: fmc )
    n [ n ] {
        ! { +nil+ [ +nil+ ] }
        { varname [| cont name | name v = [ m v cont (subst-fmc)
                                            m ensure-fmc-term (compose-fmc) ]
                   [ m v cont (subst-fmc) name <fmc-var> ] if
                  ] }
        { loc-push [| cont lpush | m v cont (subst-fmc) m v lpush
                    loc-push unboa
                    [ (subst-fmc) ] dip loc-push boa <fmc-appl> ] }
        { loc-pop  [| cont lpop | lpop var>> v =
                    [ cont lpop <fmc-abs> ]
                    [ lpop fresh-pop-subst :> ( z y lpop1 )
                      m v z y cont (subst-fmc) (subst-fmc) lpop1 <fmc-abs>
                    ] if
                   ] }
        { fmc-prim [| cont prim | m v cont (subst-fmc) prim <fmc-const> ] }
    } lmatch ;

SYMBOL: renamings
: ?var-name ( name -- name )
    name>> renamings get [ uvar ] cache
    <varname> ;
DEFER: (rename-fmc)
TYPED: rename-in-order ( cont: fmc m: fmc -- cont: fmc m: fmc )
    (rename-fmc) [ (rename-fmc) ] dip ;

TYPED: (rename-fmc) ( m: fmc -- m: fmc )
    {
        ! { +nil+ [ +nil+ ] }
        { varname [ ?var-name ] }
        { fmc-prim [ ] }
        [
            {
                { loc-pop [ [ ?var-name ] dip <loc-pop> ] }
                { loc-push [ [ (rename-fmc) ] dip <loc-push> ] }
            } match
        ]
    } fmc-cons lmatch-map-as ;

TYPED: rename-fmc ( m: fmc -- m: fmc )
    H{ } clone renamings [ (rename-fmc) ] with-variable ;

TYPED: compose-fmc ( n: fmc-term m: fmc-term -- n.m: fmc-term )
    swap
    [ [ rename-fmc ] dip (compose-fmc) ] with-var-names ;
TYPED: subst-fmc ( m: fmc-term v: varname n: fmc-term -- m/xn: fmc-term )
    [ [ rename-fmc ] dip (subst-fmc) ] with-var-names ;

ERROR: invalid-fmc-seq ;

! Used when sequence of fmc terms is expected
GENERIC: seq>proper ( seq: union{ fmc-seq-term fmc-seq } -- term: fmc-term )
! Used in sequence context
GENERIC: seq-term>proper ( seq: fmc-seq-term -- term: fmc-term )

! NOTE: converting nested code sequences to quotation pushes onto the default stack here!
TYPED: (seq>proper) ( seq: sequence -- term: fmc-term )
    <reversed> nil [
        ! dup sequence? [ seq>proper f <loc-push> ] when
        seq-term>proper
        fmc-cons swons*
    ] reduce ;

M: sequence seq>proper (seq>proper) ;
! A proper fmc-cons can be present where a sequence is expected.
M: fmc-term seq>proper ;
M: sequence seq-term>proper seq>proper f <loc-push> ;
M: fmc-seq-term seq-term>proper ;
M: loc-push seq-term>proper
    loc-push unboa [ seq>proper ] dip loc-push boa ;
M: fmc-seq-term seq>proper nil fmc-cons cons* ;

TYPED: >fmc ( obj -- term: fmc-term )
    [ >fmc* first
      seq>proper
    ] with-var-names ;

! FIXME
TYPED: proper>seq ( term: fmc-term -- seq: fmc-seq )
    list>array ;

! * Beta reduction
! Run through fmc terms in continuation form, using a term stack to perform beta
! reduction.  The resulting stack should be in sequential-term form
! TYPED: push-cont ( stack: fmc-seq cont: fmc-term m: fmc-seq-term -- stack': fmc-seq cont: fmc-term )
!     swap [ suffix ] dip ;

TYPED: blocking-loc-op? ( m: fmc-seq-term lpop: loc-pop -- ? )
    { [ drop loc-pop? ] [ [ loc>> ] same? ] } 2&& ;

! FIXME: check if blocking semantics are correct here!
TYPED: blocking-primitive? ( m: fmc-seq-term lpop: loc-pop -- ? )
    { [ drop fmc-prim? ]
      [ nip loc>> not ]
    } 2&& ;

TYPED: blocking-seq-term? ( m: fmc-seq-term lpop: loc-pop -- ? )
    {
        ! [ drop loc-op? not ]
        [ drop varname? ]
        ! [ drop prim-call? ]
        [ blocking-primitive? ]
        [ blocking-loc-op? ]
    } 2|| ;

TYPED: matching-loc-push? ( m: fmc-seq-term lpop: loc-pop -- ? )
    { [ drop loc-push? ] [ [ loc>> ] same? ] } 2&& ;

TYPED:: peek-loc ( stack: fmc-seq lpop: loc-pop -- i: maybe{ integer } m: maybe{ fmc-term } )
    stack [ lpop { [ blocking-seq-term? ] [ matching-loc-push? ] } 2|| ]
    find-last
    [ dup lpop matching-loc-push? [ body>> ] [ 2drop f f ] if ]
    [ f ] if* ;

! Search terminates:
! Found primitive -> no luck ! TODO: this can be changed if we couple
! primitives to locs for multi-machine mode?
! At least it should be true for the retain stack, since primitives could be
! substituted with push and pops on the main stack...
! Found loc-pop on different loc stack -> skip
! Found loc-push on different loc stack -> skip
! Found loc-push on same loc stack -> luck
! Found loc-pop on same loc stack -> no luck
! Found nothing -> no luck
TYPED: pop-loc ( stack: fmc-seq lpop: loc-pop -- stack: fmc-seq m: maybe{ fmc-term } )
    dupd peek-loc
    [ [ swap remove-nth ] dip ]
    [ drop f ] if* ;

! ! Performing inner reductions here.
DEFER: (beta)
TYPED: push-cont ( stack: fmc-seq cont: fmc-term m: fmc-seq-term -- stack': fmc-seq cont: fmc-term )
    dup loc-push? [ loc-push unboa [ f swap (beta) ] dip loc-push boa ] when
    swap [ suffix ] dip ;


TYPED:: find-loc-push ( stack: fmc-seq cont: fmc-term loc: loc-pop
                    --
                    stack': fmc-seq
                    cont: fmc-term
                    loc: loc-pop
                    term/f: maybe{ fmc-term } )
    stack loc pop-loc
    [ cont loc ] dip ;

TYPED: beta-subst ( m: union{ fmc-term varname } v: varname n: fmc -- m/xn: fmc )
    (subst-fmc) ;

TYPED: (beta) ( stack: fmc-seq m: fmc-term -- term: fmc-term )
    [ seq>proper ] {
        { +nil+ [ drop (beta) ] }          ! NOP
        { varname [ push-cont (beta) ] }
        { fmc-prim [ push-cont (beta) ] }
        { loc-push [ push-cont (beta) ] }
        { loc-pop [ find-loc-push
                    [| cont lpop term |
                     term lpop var>> cont beta-subst (beta)
                    ]
                    [ push-cont (beta) ] if*
                  ] }
    } lmatch ;

TYPED: beta ( term: fmc-term -- term': fmc-term )
    [ rename-fmc f swap (beta) ] with-var-names ;

! * Expansion?

! - FMC differentiates between reduction and execution phase
! - Reduction: no computation at all
! - Computation: no term manipulation
! - Could consider first pass (all passes?) as quotation-once-removed
!   Are these strategies the same?:
!   1. Beta-reduce, re-run with stacks (no interleaving)
!   2. Beta-reduce, but when pushing a primitive, actually run it (interleaving)
! - Also, for both, do we need to distinguish between:
!   1. Err when not enough items are on the stack
!   2. Ignore when not enough items are on the stack
! - Does FMC have progn semantics with respect to terms? With respect to the last
!   argument on the stack during reduction?
! - Simply quote-accumulate code on expression/literal stack? (Smells like B from SKYFEB...)
!   - e.g.: call → λ⟨x⟩ [x]ψ
!   - Strategy then: translate into code-building code
!   - beta-reduce with (partial) evaluation?
!   - Could then fetch the FMC-Sequence from ψ after the run...
!   - Would that work with both in parallel???, e.g.
!     - call → λ⟨x⟩ [x]ψ x
!     - probably not...
!     - could use that for parallel type computation, though...
!     - Also, scoping probably does not work as expected? Nested quotations?
!   - With types?
!     - ~1~ :: ~[ 1 ]ψ [ fixnum ]τ~
!     - macro semantics ~+~ :: ~ψ⟨x⟩ [x] fixnum instance? [ [ fixnum+ ]ψ ] [ [ foo+ ]ψ ] if~
!     - value-set semantics ~+~ :: ~τ⟨x⟩ [x] fixnum class<= [ fixnum+ ] [ foo+ ] ? ⟨y⟩ [y]ψ~
!     - ^ could be implemented with SKYFEB extensions, i.e. recursive macro invocations...
!   - Type-driven code-selection during reduction
!   - If reduction still has type-code left, erasure would then be performed by
!     running an eager pass on the expander code, interpreting the ~τ~ location as
!     ~[ object ] constantly~.
!   - Macro-expansion would be actual computation on main stack, but folding is
!     performed when pushing onto the ψ stack.  Could wrap this in some ~try-fold~
!     primitive, which causes evaluation if possible during beta-reduction.
!     - Folding ~+~: ~[ [ + ] try-fold ]ψ~
!   - However, more general, it is probably better to treat every unquoted word as
!     something that can be immediately executed if foldable, but when reducing
!     in expansion context, treat all computations as foldable...
!   - This approach should result in only having bare variables in a term if it is
!     not inferable

! * Conditionals
! - Need row-binders for unknown stack configurations
! - Row-binders are placed in front of quotation call sites?
! - To support imperative targets, we need to be able to run mutex branches
! - These can not have a return value.  All conditional operation results must
!   be side-effect assignments (except for the ternary conditional)
! - Alternatively, is there some kind of pattern to a call?, e.g.:
!   ~[ foo bar ] call~ → ~λ⟨a..⟩ [ [a..]λ foo bar ] λ⟨i⟩ i

! : push-outputs ( quot  )

! : linearize-if (  )

! * FMC Types, variable locations for control flow?
! - Types are indexed by location
! - Location actions, e.g. reads and writes/push/pop to other locations are
!   reflected in the signature: e.g.
!   - update cell c :: set c = ⟨x⟩.c⟨_⟩.[x]c : ℤ c(ℤ) ⇒ c(ℤ)
!   - printing :: print = ⟨x⟩.[x]out : ℤ ⇒ out(ℤ)
!   - Destructive Stream access :: rand = rnd⟨x⟩.[x] : rnd(ℤ) ⇒ ℤ
!   - ...
! - Explicit composition of lambda stacks?
! - ~[ + ] [ - ] if~
!   → [ λ₁⟨x⟩ λ₁⟨y⟩ [x]λ₁ [y]λ₁ + ]λ [ λ₂⟨x⟩ λ₂⟨y⟩ [x]λ₂ [y]λ₂ - ]λ if

!   In types: ~[ + ] [ - ]~ : (λ₁(ℤ) λ₁(ℤ) ⇒ λ₁(ℤ)) (λ₂(ℤ) λ₂(ℤ) ⇒ λ₂(ℤ)) ?

!   - Or curried, but then we need to have row variables as inference place-holders?
!   - .. [ foo ] call → .. M [ M foo ] ⟨x⟩ x
!     → [ + ] [ - ] if
!     → [ + ]λ₁ [ - ]λ₂ ⟨x⟩ if
!     → [ [y] [x] λ₁⟨x⟩ λ₁⟨y⟩ [x]λ₁ [y]λ₁ + ]λ
!       [ [y] [x] λ₂⟨x⟩ λ₂⟨y⟩ [x]λ₂ [y]λ₂ - ]λ if

!     → λ⟨x⟩ λ⟨y⟩ [ [y] [x] λ₁⟨x⟩ λ₁⟨y⟩ [x]λ₁ [y]λ₁ + ]λ
!       [ [y] [x] λ₂⟨x⟩ λ₂⟨y⟩ [x]λ₂ [y]λ₂ - ]λ if


! - Problem with control flow is that the continuation of two different
!   expressions is the same
! - Above approach could be used to write down both branches in parallel?

! * TODO Extracting location/variable info

! - Pop operations on main lambda stack can be interpreted as building a parameter
!   list, establishing locals bindings.
! - Applications on the lambda stack only make sense if they remain in applicative
!   order?
! - Primitive operations on the stack are not defined by any kind of expression,
!   only implicit using their execution semantics
! - Two approaches to build up value-level expressions
!   1. Build up quoted push actions that can be threaded as expressions
!   2. Convert lambda stack operations into per-(intermediate-)result location
!      operations, assuming mutable variables
! - Could also argue that a lobotimized piece of code(i.e. using explicitly named
!   values, variables), is a straight-line composition of effect-only loc
!   operations?  However, concatenating variable-name-dependent continuation
!   expressions seems only possible if the var access ops have already been
!   inserted with the correct names, i.e. they have to be known in each piece of
!   code beforehand.  Otherwise, how would some operation in a subsequent piece of
!   code look where to pop from?  Alternatively, invent new locations on the fly
!   for every value that needs to be identified?  How to handle unique naming
!   then?  Original FMC does not allow for passing location names...

! * Channel Semantics?
! Ref: SASL technical report
! - have streams that are
