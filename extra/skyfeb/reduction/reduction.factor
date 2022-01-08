USING: accessors arrays combinators combinators.short-circuit kernel match
sequences skyfeb typed types.util ;

IN: skyfeb.reduction

MATCH-VARS: ?o ?opq ?p ?q ?s ?t ?u ?x ?r ;

GENERIC: avoids? ( var term -- ? )
M: var avoids? name>> = not ;
M: app avoids?
    { [ left>> avoids? ] [ right>> avoids? ] } 2&& ;
M: object avoids? 2drop t ;

! NOTE: syntax:
! λx.y… = { L x { y … } }
! B y → y | x → x = { B y -> y { x -> x _ } }
DEFER: skyfeb-reduce
:: skyfeb-reduce-step ( term: object -- term: sequence ? )
    term {
        { SF{ skyfeb:B ?r } [ { skyfeb:B ?r } replace-patterns f ] }
        { SF{ Y ?t } [ ?t skyfeb-reduce :> tt { tt { Y tt } } t ] }
        { SF{ K ?s ?t } [ ?s 1array t ] }
        { SF{ S ?s ?t ?u } [ ?s skyfeb-reduce :> ss
                             ?t skyfeb-reduce :> tt
                             ?u skyfeb-reduce :> uu
                             { ss uu { tt uu } } t ] }
        { SF{ F ?opq ?s ?t } [
              ?opq skyfeb-reduce :> opq
              ?s skyfeb-reduce :> ss
              ?t skyfeb-reduce :> tt
              { { [ opq operator? ] [ { ss } t ] }
                { [ opq compound? ] [ tt opq left>> opq right>> 3array t ] }
                [ { F opq ss tt } f ]
              } cond ] }
        { SF{ E ?p ?q ?s ?t } [
              ?p skyfeb-reduce :> pp
              ?q skyfeb-reduce :> qq
              ?s skyfeb-reduce :> ss
              ?t skyfeb-reduce :> tt
              { { [ pp qq [ operator? ] both? ] [ pp qq = [ ss ] [ tt ] if 1array t ] }
                { [ pp qq [ factorable? ] both? ] [ { tt } t ] }
                [ { E pp qq ss tt } f ]
              } cond
          ] }
        ! lambda desugaring
        { SF{ I } [ { S K K } t ] }
        { SF{ L VAR{ ?x } { VAR{ ?x } } } [ { I } t ] }
        { SF{ L VAR{ ?x } { ?t } } [
              ?t skyfeb-reduce :> tt
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
           ?p skyfeb-reduce :> pp
           ?q skyfeb-reduce :> qq
           ?r skyfeb-reduce :> rr
           ?s skyfeb-reduce :> ss
           { S { K rr } } :> rr'
           { L xx { F xx { rr xx }
                    { L yy { { pp -> { qq -> ss { rr' } { yy } } { rr' } } yy } } } }
           t
          ] }
        { SF{ ?o -> ?s { ?r } }
          [ ?o :> oo
            ?s :> ss
            "x" uvar <var> :> xx
            oo operator?
            [
                ?r skyfeb-reduce :> rr
                ss skyfeb-reduce :> ss
                { L xx { E oo xx ss { rr xx } } } t
            ] [ { L oo ss } t ] if
          ] }
        { SF{ ?p ?q } [
              ?p skyfeb-reduce-step :> ( pp p? )
              ?q skyfeb-reduce-step :> ( qq q? )
              pp >skyfeb qq >skyfeb <app> p? q? or
          ] }
        [ 1array f ]
    } match-cond ;

: re ( term: term -- term: term )
    skyfeb-reduce-step drop >skyfeb ;

: skyfeb-reduce ( term: object -- term: object )
    [ skyfeb-reduce-step [ >skyfeb ] dip ] loop ;
