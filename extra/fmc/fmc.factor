USING: accessors arrays combinators compiler.tree.debugger effects kernel
namespaces quotations sequences sets strings typed types.util variants words ;

IN: fmc

! * Willem Heijltjes Functional Machine Calculus

! VARIANT: lc-term
!     lc-appl: { left right }
!     lc-abstr: { var body }
! Two ways of representing: ordered list of term-parts
! Composition of objects
VARIANT: fmc-term
    +unit+
    varname: { { name string } }
    loc-push: { body { loc maybe{ word } } }
    loc-pop: { { var maybe{ varname } } { loc maybe{ word } } }
    fmc-prim: { obj }
    fmc-var: { { cont fmc-term } { var maybe{ union{ varname fmc-prim } } } }
    ! fmc-const: { { prim fmc-prim } { cont fmc-term } }
    fmc-appl: { { cont fmc-term } { push loc-push } }
    fmc-abs: { { cont fmc-term } { pop loc-pop } }
    ;

SINGLETON: +retain+
UNION: fmc-seq-term sequence fmc-term ;
PREDICATE: fmc-seq < sequence [ fmc-seq-term? ] all? ;
UNION: fmc-proper +unit+ ! fmc-const
    fmc-var fmc-appl fmc-abs ;
UNION: fmc fmc-seq fmc-proper ;

GENERIC: >fmc* ( object -- term: fmc )
TYPED: <fmc-const> ( obj -- e: fmc-seq ) <fmc-prim> 1array ;
M: object >fmc* <fmc-const> ;

M: quotation >fmc* [ >fmc* ] map concat 1array ;
PREDICATE: shuffle-word < word "shuffle" word-prop ;

SYMBOL: word-stack

TYPED: word-intro ( word -- term: fmc )
    stack-effect effect-in-names
    [ uvar <varname> ] map
    [ [ f <loc-pop> ] map ]
    [ <reversed> [ f <loc-push> ] map ] bi append ;

! TYPED: word-inst ( body word --  term: fmc )
!     name>> uvar f loc-pop 1quotation

! TODO: recursive
! TYPED: recursive>fmc ( word -- term: fmc )

TYPED: exec>fmc ( word -- term: fmc )
    [ word-intro ]
    [ def>> >fmc* ] bi append ;

TYPED: shuffle>fmc ( word -- term: fmc )
    "shuffle" word-prop
    [ in>> ] [ out>> ] bi uvar-shuffle
    [ [ <varname> ] map ] bi@
    [ [ f <loc-pop> ] map ]
    [ <reversed> [ f <loc-push> ] map ] bi* append ;

ERROR: recursive-fmc word ;

TYPED: word>fmc ( word -- term: fmc )
    dup word-stack get in? [ recursive-fmc ] when
    { { [ dup shuffle-word? ] [ shuffle>fmc ] }
      { [ dup primitive? ] [ <fmc-const> ] }
      { [ dup { call } in? ] [ <fmc-const> ] }
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


! * Term operations

! Compose N;M -> (N.M)
DEFER: subst-fmc
TYPED: <fresh> ( n: varname -- n': varname )
    name>> uvar <varname> ;
TYPED: fresh-pop ( pop: loc-pop -- pop': loc-pop )
    loc-pop unboa [ <fresh> ] dip loc-pop boa ;
TYPED: fresh-pop-subst ( pop: loc-pop -- fresh: fmc-var old: fmc-var pop': loc-pop )
    dup fresh-pop
    [ [ var>> ] bi@ ] keep ;

TYPED: compose-fmc ( m: fmc-proper n: fmc-proper -- n.m: fmc-proper )
    { { +unit+ [ ] }
      { fmc-var [ [ compose-fmc ] dip <fmc-var> ] }
      { fmc-appl [ [ compose-fmc ] dip <fmc-appl> ] }
      { fmc-abs [ fresh-pop-subst [ rot subst-fmc compose-fmc ] dip <fmc-abs> ] }
    } match ;

TYPED:: subst-fmc ( m: fmc-proper v: fmc-var n: fmc-proper -- m/xn: fmc-proper )
    n { { +unit+ [ +unit+ ] }
      { fmc-var [| cont name | name v name>> = [ m m v cont subst-fmc compose-fmc ]
                 [ m v cont subst-fmc name <fmc-var> ] if
                ] }
      { fmc-appl [| cont lpush | m v cont subst-fmc m v lpush subst-fmc <fmc-appl> ] }
      { loc-push [| body loc | m v body subst-fmc loc <loc-push> ] }
      { fmc-abs  [| cont lpop | lpop var>> v =
                   [ cont lpop <fmc-abs> ]
                   [ lpop fresh-pop-subst :> ( z y lpop1 )
                     m v z y cont subst-fmc subst-fmc lpop1 <fmc-abs>
                   ] if
                  ] }
    } match ;

ERROR: invalid-fmc-seq ;
TYPED: seq>proper ( seq: fmc-seq -- term: fmc-proper )
    [ +unit+ ]
    [ unclip-slice
      {
          { +unit+ [ invalid-fmc-seq ] }
          { varname [ <varname> [ seq>proper ] dip <fmc-var> ] }
          { loc-push [ <loc-push> [ seq>proper ] dip <fmc-appl> ] }
          { loc-pop [ <loc-pop> [ seq>proper ] dip <fmc-abs> ] }
          { fmc-prim [ <fmc-prim> [ seq>proper ] dip <fmc-var> ] }
          ! TODO: support composition
          [ dup sequence? [ [ seq>proper ] bi@ f <loc-push> <fmc-appl> ]
            [ invalid-fmc-seq ] if ]
      } match
    ] if-empty ;

TYPED: >fmc ( obj -- term: fmc-proper )
    >fmc* first
    seq>proper ;

TYPED: proper>seq ( term: fmc-proper -- seq: fmc-seq )
    {
        { +unit+ [ f ] }
        { fmc-var [ [ proper>seq ] dip prefix ] }
        { fmc-abs [ [ proper>seq ] dip prefix ] }
        { fmc-appl [ [ proper>seq ] dip prefix ] }
    } match ;

! * Beta reduction
! Walk from left to right through expression
! For each term:
! - If substitution defined, no substitution defined, store itself as substitution
! - If an application: push to stack
! - If an abstraction-pop x: try to pop from stack A
!   - If stack empty, do nothing
!   - Otherwise, pop M from stack A, set substitution of M to f, set substitution of x to M


! TYPED: substitute ( subst: assoc term: fmc )





! TYPED:: (beta) ( stacks bindings term: fmc -- n: fmc )
!     term {
!         { +unit+ [ +unit+ ] }
!         { varname [ over at? [ [ swap pluck-at ] dip (beta) ] [ <varname> ] if ] }
!         { loc-push }
!     } match ;

! TYPED: subst ( repl: assoc e: fmc -- term: fmc )
!     {
!         {  }
!         [ nip ]
!     } match

! SYMBOLS: stacks bindings ;
! : (beta) ( fmc -- )
!     [
!         [
!             {
!                 { loc-push stacks }
!                 [ drop ]
!             } match
!         ] each
!     ] over ;
