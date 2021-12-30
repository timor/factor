USING: accessors arrays assocs combinators combinators.short-circuit
compiler.tree.debugger effects kernel math namespaces quotations sequences sets
strings typed types.util variants words ;

IN: fmc

! * Willem Heijltjes Functional Machine Calculus

! Two ways of representing: ordered list of term-parts, or tree of binary terms

TUPLE: varname { name string } ;
C: <varname> varname
TUPLE: fmc-prim obj ;
C: <fmc-prim> fmc-prim
TUPLE: loc-push body { loc maybe{ word } } ;
C: <loc-push> loc-push
TUPLE: loc-pop { var maybe{ varname } } { loc maybe{ word } } ;
C: <loc-pop> loc-pop
UNION: loc-op loc-push loc-pop ;

VARIANT: fmc-term
    +unit+
    fmc-var: { { cont fmc-term } { var maybe{ union{ varname fmc-prim } } } }
    fmc-appl: { { cont fmc-term } { push loc-push } }
    fmc-abs: { { cont fmc-term } { pop loc-pop } }
    ;

SINGLETON: +retain+
UNION: fmc-seq-term ! fmc-term
    varname fmc-prim loc-push loc-pop ;
PREDICATE: fmc-seq < sequence [ fmc-seq-term? ] all? ;
UNION: fmc fmc-seq-term fmc-term ;

GENERIC: >fmc* ( object -- term: fmc-seq )
TYPED: <const> ( obj -- e: fmc-seq ) <fmc-prim> 1array ;
M: object >fmc* <const> ;
PREDICATE: fmc-const < fmc-var var>> fmc-prim? ;

M: quotation >fmc* [ >fmc* ] map concat 1array ;
PREDICATE: shuffle-word < word "shuffle" word-prop ;

SYMBOL: word-stack

TYPED: word-intro ( word -- term: fmc-seq )
    stack-effect effect-in-names
    [ uvar <varname> ] map
    [ [ f <loc-pop> ] map ]
    [ <reversed> [ f <loc-push> ] map ] bi append ;

! TYPED: word-inst ( body word --  term: fmc )
!     name>> uvar f loc-pop 1quotation

! TODO: recursive
! TYPED: recursive>fmc ( word -- term: fmc )

TYPED: exec>fmc ( word -- term: fmc-seq )
    [ word-intro ]
    [ def>> >fmc* first ] bi append ;

TYPED: shuffle>fmc ( word -- term: fmc-seq )
    "shuffle" word-prop
    [ in>> ] [ out>> ] bi uvar-shuffle
    [ [ <varname> ] map ] bi@
    [ [ f <loc-pop> ] map ]
    [ <reversed> [ f <loc-push> ] map ] bi* append ;

ERROR: recursive-fmc word ;

TYPED: word>fmc ( word -- term: fmc-seq )
    dup word-stack get in? [ recursive-fmc ] when
    { { [ dup shuffle-word? ] [ shuffle>fmc ] }
      { [ dup primitive? ] [ <const> ] }
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
    [ f <loc-pop> ] keep 2array ;

! Takes two args from the stack
! Top-most is a callable
! Below that is an object
! When called: 1. push object
! 2. Call callable
M: \ curry >fmc* drop
    [let
     "o" uvar <varname> :> o
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
    { { +unit+ [ ] }
      { fmc-var [ [ (compose-fmc) ] dip <fmc-var> ] }
      { fmc-appl [ [ (compose-fmc) ] dip <fmc-appl> ] }
      { fmc-abs [ fresh-pop-subst [ rot (subst-fmc) (compose-fmc) ] dip <fmc-abs> ] }
    } match ;

! If we carry over a var-name, then it is composed as a single fmc-var
TYPED: ensure-fmc-term ( m: fmc -- m': fmc-term )
    dup varname? [ +unit+ swap <fmc-var> ] when ;
TYPED:: (subst-fmc) ( m: union{ fmc-term varname } v: varname n: fmc -- m/xn: fmc )
    n { { +unit+ [ +unit+ ] }
        { fmc-var [| cont name | name v = [ m v cont (subst-fmc)
                                            m ensure-fmc-term (compose-fmc) ]
                 [ m v cont (subst-fmc) name <fmc-var> ] if
                ] }
      { fmc-appl [| cont lpush | m v cont (subst-fmc) m v lpush (subst-fmc) <fmc-appl> ] }
      { loc-push [| body loc | m v body (subst-fmc) loc <loc-push> ] }
      { fmc-abs  [| cont lpop | lpop var>> v =
                   [ cont lpop <fmc-abs> ]
                   [ lpop fresh-pop-subst :> ( z y lpop1 )
                     m v z y cont (subst-fmc) (subst-fmc) lpop1 <fmc-abs>
                   ] if
                  ] }
    } match ;

SYMBOL: renamings
: ?var-name ( name -- name )
    renamings get [ uvar ] cache ;
DEFER: (rename-fmc)
TYPED: rename-in-order ( cont: fmc m: fmc -- cont: fmc m: fmc )
    (rename-fmc) [ (rename-fmc) ] dip ;

TYPED: (rename-fmc) ( m: fmc -- m: fmc )
    { { +unit+ [ +unit+ ] }
      { fmc-var [ rename-in-order <fmc-var> ] }
      { fmc-appl [ rename-in-order <fmc-appl> ] }
      { fmc-abs [ rename-in-order <fmc-abs> ] }
      { fmc-prim [ <fmc-prim> ] }
      { varname [ ?var-name <varname> ] }
      { loc-pop [ [ (rename-fmc) ] dip <loc-pop> ] }
      { loc-push [ [ (rename-fmc) ] dip <loc-push> ] }
    } match ;

TYPED: rename-fmc ( m: fmc -- m: fmc )
    H{ } clone renamings [ (rename-fmc) ] with-variable ;

TYPED: compose-fmc ( n: fmc-term m: fmc-term -- n.m: fmc-term )
    swap
    [ [ rename-fmc ] dip (compose-fmc) ] with-var-names ;
TYPED: subst-fmc ( m: fmc-term v: varname n: fmc-term -- m/xn: fmc-term )
    [ [ rename-fmc ] dip (subst-fmc) ] with-var-names ;

ERROR: invalid-fmc-seq ;

GENERIC: seq-term>proper ( seq: fmc-seq-term -- term: fmc-term )
! TYPED: seq>proper ( seq: fmc-seq -- term: fmc-term )
TYPED: seq>proper ( seq: sequence -- term: fmc-term )
    [ +unit+ ]
    [ unclip-slice
      {
          { +unit+ [ invalid-fmc-seq ] }
          { varname [ <varname> [ seq-term>proper ] dip <fmc-var> ] }
          { loc-push [ [ [ seq-term>proper ] bi@ ] dip <loc-push> <fmc-appl> ] }
          { loc-pop [ <loc-pop> [ seq-term>proper ] dip <fmc-abs> ] }
          { fmc-prim [ <fmc-prim> [ seq-term>proper ] dip <fmc-var> ] }
          [ dup sequence? [ [ seq-term>proper ] bi@ f <loc-push> <fmc-appl> ]
            [ invalid-fmc-seq ] if ]
      } match
    ] if-empty ;

M: fmc-term seq-term>proper ;
M: sequence seq-term>proper seq>proper ;
M: fmc-seq-term seq-term>proper
    1array seq>proper ;

TYPED: >fmc ( obj -- term: fmc-term )
    [ >fmc* first
      seq-term>proper ] with-var-names ;

! FIXME
TYPED: proper>seq ( term: fmc-term -- seq: fmc-seq )
    {
        { +unit+ [ f ] }
        { fmc-var [ [ proper>seq ] dip prefix ] }
        { fmc-abs [ [ proper>seq ] dip prefix ] }
        { fmc-appl [ [ proper>seq ] dip prefix ] }
    } match ;

! * Beta reduction
! Run through fmc terms in continuation form, using a term stack to perform beta
! reduction.  The resulting stack should be in sequential-term form
! TYPED: push-cont ( stack: fmc-seq cont: fmc-term m: fmc-seq-term -- stack': fmc-seq cont: fmc-term )
!     swap [ suffix ] dip ;

TYPED: blocking-loc-op? ( m: fmc-seq-term lpop: loc-pop -- ? )
    { [ drop loc-pop? ] [ [ loc>> ] same? ] } 2&& ;

TYPED: blocking-seq-term? ( m: fmc-seq-term lpop: loc-pop -- ? )
    {
        [ drop loc-op? not ]
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
! primitives to locs for multi-machine mode
! Found loc-pop on different loc stack -> skip
! Found loc-push on different loc stack -> skip
! Found loc-push on same loc stack -> luck
! Found loc-pop on same loc stack -> no luck
! Found nothing -> no luck
TYPED: pop-loc ( stack: fmc-seq lpop: loc-pop -- stack: fmc-seq m: maybe{ fmc-term } )
    dupd peek-loc
    [ [ swap remove-nth ] dip ]
    [ drop f ] if* ;

! TYPED: inline-call? ( stack: fmc-seq m: fmc-seq-term -- stack: fmc-seq m: maybe{ fmc-term } )
!     dup call-primop?
!     [ over peek-lambda
!       [ [ nip swap remove-nth ] dip ]
!       [ drop f ] if* ]
!     [ drop f ] if ;

! DEFER: (beta)
! TYPED:: maybe-inline-call ( stack: fmc-seq
!                             cont: fmc-term
!                             m: fmc-seq-term
!                                 --
!                                 stack': fmc-seq
!                                 cont: fmc-term
!                                 m: maybe{ fmc-seq-term } )
!     stack m inline-call?
!     [ (beta) cont f ]
!     [ cont m ] if* ;

TYPED: push-cont ( stack: fmc-seq cont: fmc-term m: fmc-seq-term -- stack': fmc-seq cont: fmc-term )
    ! maybe-inline-call
    ! [ swap [ suffix ] dip ] when* ;
    swap [ suffix ] dip ;


TYPED:: find-loc-push ( stack: fmc-seq cont: fmc-term loc: loc-pop
                    --
                    stack': fmc-seq
                    cont: fmc-term
                    loc: loc-pop
                    term/f: maybe{ fmc-term } )
    stack loc pop-loc
    [ cont loc ] dip ;

! TYPED:: beta-subst ( m: union{ fmc-term varname } v: varname n: fmc -- m/xn: fmc )
!     (subst-fmc) ;

TYPED: (beta) ( stack: fmc-seq m: fmc-term -- stack: fmc-seq )
    {
        { +unit+ [ ] }          ! NOP
        { fmc-var [ push-cont (beta) ] }
        { fmc-appl [ push-cont (beta) ] }
        { fmc-abs [ find-loc-push
                    [| cont lpop term |
                     term lpop var>> cont (subst-fmc) (beta)
                    ]
                    [ push-cont (beta) ] if*
                  ] }
    } match ;

TYPED: beta ( term: fmc-term -- term': fmc-term )
    [ rename-fmc f swap (beta) ] with-var-names
    seq>proper ;
