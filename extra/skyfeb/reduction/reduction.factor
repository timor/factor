USING: accessors arrays combinators combinators.short-circuit kernel match
memoize sequences skyfeb typed types.util ;

IN: skyfeb.reduction

MATCH-VARS: ?f ?o ?opq ?p ?q ?s ?t ?u ?x ?r ;

GENERIC: avoids? ( var term -- ? )
M: var avoids? name>> = not ;
M: app avoids?
    { [ left>> avoids? ] [ right>> avoids? ] } 2&& ;
M: object avoids? 2drop t ;

! NOTE: syntax:
! λx.y… = { L x { y … } }
! B y → y | x → x = { B y -> y { x -> x _ } }
DEFER: (skyfeb-reduce)
:: skyfeb-reduce-step ( term: object -- term: sequence ? )
    term {
        { SF{ skyfeb:B ?r } [ { skyfeb:B ?r } replace-patterns f ] }
        ! This should ensure that if the only thing that is expanded is a Y
        ! combinator, we don't run into an infinite loop during expansion, even
        ! if there is nothing to block it...
        ! { SF{ Y ?t } [ ?t (skyfeb-reduce) :> tt { tt { Y tt } } f ] }
        ! Reduce Y bodies, but don't consider as changed
        { SF{ Y ?t } [ ?t (skyfeb-reduce) :> tt { Y tt } f ] }
        ! Exception: only reduce y combinator if it has an argument
        { SF{ { Y ?t } ?u } [
              ?t (skyfeb-reduce) :> tt
              ?u (skyfeb-reduce) :> uu
              { { tt { Y tt } } uu } t ] }
        { SF{ K ?s ?t } [ ?s 1array t ] }
        { SF{ S ?s ?t ?u } [ ?s (skyfeb-reduce) :> ss
                             ?t (skyfeb-reduce) :> tt
                             ?u (skyfeb-reduce) :> uu
                             { ss uu { tt uu } } t ] }
        { SF{ F ?opq ?s ?t } [
              ?opq (skyfeb-reduce) :> opq
              ?s (skyfeb-reduce) :> ss
              ?t (skyfeb-reduce) :> tt
              { { [ opq operator? ] [ { ss } t ] }
                { [ opq compound? ] [ tt opq left>> opq right>> 3array t ] }
                [ { F opq ss tt } f ]
              } cond ] }
        { SF{ E ?p ?q ?s ?t } [
              ?p (skyfeb-reduce) :> pp
              ?q (skyfeb-reduce) :> qq
              ?s (skyfeb-reduce) :> ss
              ?t (skyfeb-reduce) :> tt
              { { [ pp qq [ operator? ] both? ] [ pp qq = [ ss ] [ tt ] if 1array t ] }
                { [ pp qq [ factorable? ] both? ] [ { tt } t ] }
                [ { E pp qq ss tt } f ]
              } cond
          ] }
        ! lambda desugaring
        { SF{ I } [ { S K K } t ] }
        { SF{ L VAR{ ?x } { VAR{ ?x } } } [ { I } t ] }
        { SF{ L VAR{ ?x } { ?t } } [
              ?t (skyfeb-reduce) :> tt
              ?x tt avoids? [ { K tt } t ] [
                  ?x <var> :> xx
                  tt app? [
                      tt [ left>> ] [ right>> ] bi :> ( rr uu )
                      { [ xx uu = ] [ ?x rr avoids? ] } 0&&
                      [ { rr } t ]
                      [ { S { L xx { rr } } { L xx { uu } } } t ] if
                  ] [ { L xx { tt } } f ] if
              ] if
          ] }
        ! desugar extensions
        { SF{ { ?p ?q } -> ?s { ?r } }
          [ "x" uvar <var> :> xx
           "y" uvar <var> :> yy
           ?p (skyfeb-reduce) :> pp
           ?q (skyfeb-reduce) :> qq
           ?r (skyfeb-reduce) :> rr
           ?s (skyfeb-reduce) :> ss
           { S { K rr } } :> rr'
           { L xx { F xx { rr xx }
                    { L yy { { pp -> { qq -> ss { rr' yy } } { rr' } } yy } } } }
           t
          ] }
        { SF{ ?o -> ?s { ?r } }
          [ ?o :> oo
            ?s :> ss
            "x" uvar <var> :> xx
            oo operator?
            [
                ?r (skyfeb-reduce) :> rr
                ss (skyfeb-reduce) :> ss
                { L xx { E oo xx ss { rr xx } } } t
            ] [ { L oo ss } t ] if
          ] }
        { SF{ VAR{ ?x } -> ?s } [
              ?x <var> :> xx
              ?s (skyfeb-reduce) :> ss
              { L xx ss } t
          ] }
        ! let bindings
        { SF{ let VAR{ ?x } { ?u } { ?t } } [
              ?x <var> :> xx
              ?u (skyfeb-reduce) :> uu
              ?t (skyfeb-reduce) :> tt
              { { L xx { tt } } uu } t
          ] }
        { SF{ letrec VAR{ ?f } ?t } [
              ?f <var> :> ff
              ?t (skyfeb-reduce) :> tt
              { Y { L ff { tt } } } t
          ] }
        ! Recurse
        { SF{ ?p ?q } [
              ?p skyfeb-reduce-step :> ( pp p? )
              ?q skyfeb-reduce-step :> ( qq q? )
              pp >skyfeb qq >skyfeb <app> p? q? or
          ] }
        ! NOTE: relying on predicate return arg here!
        [ dup skyfeb-word? [ nip skyfeb-reduce-step ] [ 1array f ] if* ]
    } match-cond ;

: re ( term: term -- term: term )
    skyfeb-reduce-step drop >skyfeb ;

MEMO: (skyfeb-reduce) ( term: object -- term: object )
    [ skyfeb-reduce-step [ >skyfeb ] dip ] loop ;

: skyfeb-reduce ( term: object -- term: object )
    \ (skyfeb-reduce) reset-memoized
    (skyfeb-reduce) ;

! : (skyfeb-reduce) ( term: object -- term: object )
!     [ skyfeb-reduce-step [ >skyfeb ] dip ] loop ;



! CONSTANT: equal-test
SKY: equal { letrec "equal" { "x1" "x2" ->
                     { "y1" "y2" -> { { "equal" "x1" "y1" } { "equal" "x2" "y2" } { K I } } { "y3" -> { K I } "foo2" } }
                     { "x" -> { "y" -> { E "x" "y" K { K I } } "foo" } "foo" } } }
