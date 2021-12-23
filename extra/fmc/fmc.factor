USING: accessors arrays assocs combinators compiler.tree.debugger effects kernel
namespaces quotations sequences sets strings typed types.util variants words ;

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

VARIANT: fmc-term
    +unit+
    fmc-var: { { cont fmc-term } { var maybe{ union{ varname fmc-prim } } } }
    fmc-appl: { { cont fmc-term } { push loc-push } }
    fmc-abs: { { cont fmc-term } { pop loc-pop } }
    ;

SINGLETON: +retain+
UNION: fmc-seq-term fmc-term varname fmc-prim loc-push loc-pop ;
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
      { [ dup { call } in? ] [ <const> ] }
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
        { fmc-var [| cont name | name v = [ m ensure-fmc-term
                                            m v cont (subst-fmc) (compose-fmc) ]
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
! TYPED: beta ( term: fmc-term -- fmc-term )
! TUPLE: state { memory assoc } { term fmc } ;
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
