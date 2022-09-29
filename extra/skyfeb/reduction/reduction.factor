USING: accessors arrays combinators combinators.short-circuit continuations
kernel match memoize namespaces sequences skyfeb typed types.util words ;

IN: skyfeb.reduction

MATCH-VARS: ?f ?o ?opq ?p ?q ?s ?t ?u ?x ?r ;
FROM: skyfeb => B L A ;

GENERIC: avoids? ( var term -- ? )
M: var avoids? name>> = not ;
M: app avoids?
    { [ left>> avoids? ] [ right>> avoids? ] } 2&& ;
M: object avoids? 2drop t ;

! NOTE: syntax:
! λx.y… = { L x { y … } }
! B y → y | x → x = { B y -> y { x -> x _ } }
DEFER: (skyfeb-reduce)

DEFER: must-desugar
DEFER: may-desugar
: eta-contraction? ( term -- term/f )
    SF{ L VAR{ ?x } { ?t VAR{ ?x } } } match dup
    [ [ ?x ?t avoids? [ ?t ] [ f ] if ] with-variables ] when ;

: desugar ( term -- term ? )
    ! dup
    dup eta-contraction?
    [ nip t ]
    [
        {
            ! lambda desugaring
            { SF{ L VAR{ ?x } { VAR{ ?x } } } [ SF{ I } t ] }
            ! { SF{ L VAR{ ?x } { ?t } { ?u } }
            !   [| |
            !    ?t desugar :> tt
            !    ?u desugar :> uu
            !    ?x <var> :> xx
            !    ?x

            !   ]
            ! }

            { SF{ L VAR{ ?x } { ?t } } [| |
                                        ?t may-desugar :> tt
                                        ?x tt avoids? [ ! tt desugar :> tt
                                            SF{ K tt } t ] [
                                            ?x <var> :> xx
                                            ! tt desugar :> tt
                                            tt app? [
                                                tt [ left>> ] [ right>> ] bi :> ( rr uu )
                                                { [ xx uu = ] [ ?x rr avoids? ] } 0&&
                                                ! drop f
                                                [ ! rr desugar :> rr
                                                    SF{ rr } t ]
                                                [ ! rr  desugar :> rr
                                                    ! uu  desugar :> uu
                                                    SF{ L xx { rr } } must-desugar :> l1
                                                    SF{ L xx { uu } } must-desugar :> l2
                                                    SF{ S l1 l2 } t ] if
                                            ] [ f f ] if
                                        ] if
                                       ] }
            ! desugar extensions
            { SF{ { ?p ?q } -> ?s { ?r } }
              [| |
               "x" uvar <var> :> xx
               "y" uvar <var> :> yy
               ?p :> pp
               ?q :> qq
               ?s may-desugar :> ss
               ?r may-desugar :> rr
               SF{ S { K rr } } :> rr'
               SF{ L yy { { pp -> { qq -> ss { rr' yy } } { rr' } } yy } } must-desugar :> l2
               SF{ L xx { F xx { rr xx } l2 } } must-desugar t
               ! SF{ L xx { F xx { rr xx }
               !           { L yy { { pp -> { qq -> ss { rr' yy } } { rr' } } yy } } } } desugar
               ! SF{ l1 l2 } t
              ] }
            { SF{ ?o -> ?s { ?r } }
              [| |
               ?o :> oo
               ?s :> ss
               "x" uvar <var> :> xx
               oo operator?
               [
                   ss may-desugar :> ss
                   ?r ! may-desugar
                   :> rr
                   SF{ L xx { E oo xx ss { rr xx } } } must-desugar
               ] [ SF{ L oo ss } must-desugar ] if
               t
              ] }
            { SF{ VAR{ ?x } -> ?s }
              [| |
               ?x <var> :> xx
               ?s :> ss
               SF{ L xx ss } must-desugar t
              ] }
            ! desugar bindings
            { SF{ let VAR{ ?x } { ?u } { ?t } }
              [| |
               ?x <var> :> xx
               ?u may-desugar :> uu
               ?t :> tt
               SF{ L xx { tt } } must-desugar :> l1
               SF{ l1 uu } t
              ] }
            { SF{ letrec VAR{ ?f } ?t }
              [| |
               ?f <var> :> ff
               ?t :> tt
               SF{ L ff { tt } } must-desugar :> l1
               SF{ Y l1 } t
              ] }
            [ f ]
        } match-cond
        ! 2dup eta-contraction? [ spin drop ] [ drop ] if
    ] if* ;
    ! [ nip ] when* ;

: may-desugar ( term -- term )
    desugar drop ;
: must-desugar ( term -- term )
    desugar [ "must-desugar" 2array throw ] unless ;

:: skyfeb-reduce-step ( term: object -- term: sequence ? )
    term dup {
        ! { SF{ B ?r } [ f f ] }
        ! This should ensure that if the only thing that is expanded is a Y
        ! combinator, we don't run into an infinite loop during expansion, even
        ! if there is nothing to block it...
        ! { SF{ Y ?t } [ ?t (skyfeb-reduce) :> tt { tt { Y tt } } f ] }
        ! Reduce Y bodies, but don't consider as changed
        ! { SF{ Y ?t } [ ?t (skyfeb-reduce) :> tt { Y tt } f ] }
        ! Exception: only reduce y combinator if it has an argument
        ! NOTE: might need to have to replace this with wait combinator?
        { SF{ { Y ?t } ?u } [
              ?t (skyfeb-reduce) :> tt
              ?u (skyfeb-reduce) :> uu
              { { tt { Y tt } } uu } t ] }
        ! ! Using wait combinator
        ! { SF{ Y ?t } [
        !       ?t (skyfeb-reduce) :> tt
        !       { tt { A Y tt } }  t ] }
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
                [ f f ]
              } cond ] }
        { SF{ E ?p ?q ?s ?t } [
              ?p (skyfeb-reduce) :> pp
              ?q (skyfeb-reduce) :> qq
              ?s (skyfeb-reduce) :> ss
              ?t (skyfeb-reduce) :> tt
              { { [ pp qq [ operator? ] both? ] [ pp qq = [ ss ] [ tt ] if 1array t ] }
                { [ pp qq [ factorable? ] both? ] [ { tt } t ] }
                [ f f ]
              } cond
          ] }
        ! { SF{ BB } }
        ! Lazy evaluation
        { SF{ A ?r ?s ?t } [
              ?r (skyfeb-reduce) :> rr
              ?s (skyfeb-reduce) :> ss
              ?t (skyfeb-reduce) :> tt
              { rr ss tt } t
          ] }
        ! Block partials!
        { SF{ A ?r ?s } [ f f ] }
        { SF{ A ?r } [ f f ] }
        { SF{ I ?t } [ ?t (skyfeb-reduce) t ] }
        { SF{ BB ?r ?s ?t } [ SF{ ?r { ?s ?t } } replace-patterns t ] }
        { SF{ C ?r ?s ?t } [ SF{ ?r ?t ?s } replace-patterns t ] }
        { SF{ W ?r ?s } [ SF{ ?r ?s ?s } replace-patterns t ] }
        { SF{ M ?r } [ SF{ ?r ?r } replace-patterns t ] }
        { SF{ T ?r ?s } [ SF{ ?s ?r } replace-patterns t ] }
        { SF{ AA ?r ?s } [ ?s t ] }
        ! ! desugar extensions
        ! { SF{ { ?p ?q } -> ?s { ?r } }
        !   [ "x" uvar <var> :> xx
        !    "y" uvar <var> :> yy
        !    ?p (skyfeb-reduce) :> pp
        !    ?q (skyfeb-reduce) :> qq
        !    ?r (skyfeb-reduce) :> rr
        !    ?s (skyfeb-reduce) :> ss
        !    { S { K rr } } :> rr'
        !    { L xx { F xx { rr xx }
        !             { L yy { { pp -> { qq -> ss { rr' yy } } { rr' } } yy } } } }
        !    t
        !   ] }
        ! { SF{ ?o -> ?s { ?r } }
        !   [ ?o :> oo
        !     ?s :> ss
        !     "x" uvar <var> :> xx
        !     oo operator?
        !     [
        !         ?r (skyfeb-reduce) :> rr
        !         ss (skyfeb-reduce) :> ss
        !         { L xx { E oo xx ss { rr xx } } } t
        !     ] [ { L oo ss } t ] if
        !   ] }
        ! { SF{ VAR{ ?x } -> ?s } [
        !       ?x <var> :> xx
        !       ?s (skyfeb-reduce) :> ss
        !       { L xx ss } t
        !   ] }
        ! eta contraction
        { SF{ L VAR{ ?x } { ?s VAR{ ?x } } } [| |
                                              ?x ?s avoids?
                                              [ ?s t ]
                                              [ ?x <var> :> xx
                                                ?s :> ss
                                                SF{ L xx { ss xx } } must-desugar t
                                              ] if
                                             ] }
        [
            ! catch syntax-sugar
            { { [ dup skyfeb-word? ] [ "skyfeb-def" word-prop t ] }
              { [ dup SF{ let ?r ?s ?t } match ] [ must-desugar t ] }
              { [ dup SF{ letrec ?r ?s } match ] [ must-desugar t ] }
              { [ dup SF{ L ?r ?s } match ] [ must-desugar t ] }
              { [ dup SF{ ?r -> ?s ?t } match ] [ must-desugar t ] }
              { [ dup SF{ ?r -> ?s } match ] [ must-desugar t ] }
              [
                ! Recurse
                  {
                      { SF{ ?p ?q } [
                            ! ?p { [ skyfeb-word? ] [ skyfeb-term? ] } 1|| not [ ?p "invalid term" 2array throw ] when
                            ?p skyfeb-reduce-step :> ( pp p? )
                            ?q skyfeb-reduce-step :> ( qq q? )
                            pp >skyfeb qq >skyfeb <app> p? q? or
                        ] }
                      [ f ]
                  } match-cond
              ]

            } cond

            ! dup skyfeb-word? [ nip ! [ A I ] dip 3array
            !                    t ] [ f ] if*
        ]
        ! [ f ]
    } match-cond
    [ nip t ] [ drop f ] if
    ;

: re ( term: term -- term: term )
    skyfeb-reduce-step drop >skyfeb ;

IDENTITY-MEMO: (skyfeb-reduce) ( term: object -- term: object )
! ! : (skyfeb-reduce) ( term: object -- term: object )
    [ skyfeb-reduce-step [ >skyfeb ] dip ] loop ;
! : (skyfeb-reduce) ( term -- term ) ;

! TODO: maybe be bold and not reset memoization? Like, ever?
: skyfeb-reduce ( term: object -- term: object )
    ! \ (skyfeb-reduce) reset-memoized
    ! [ skyfeb-reduce-step [ >skyfeb ] dip ] loop ;
    (skyfeb-reduce) ;

! ALIAS: desugar skyfeb-reduce

! : (skyfeb-reduce) ( term: object -- term: object )
!     [ skyfeb-reduce-step [ >skyfeb ] dip ] loop ;



! CONSTANT: equal-test
SKY: equal { letrec "equal" { "x1" "x2" ->
                     ! { "y1" "y2" -> { { "equal" "x1" "y1" } { "equal" "x2" "y2" } { K I } } { "y3" -> { K I } "foo2" } }
                     ! { "x" -> { "y" -> { E "x" "y" K { K I } } "foo" } "foo" } } }
                     { "y1" "y2" -> { { "equal" "x1" "y1" } { "equal" "x2" "y2" } { K I } } { "y3" -> { K I } } }
                     { "x" -> { "y" -> { E "x" "y" K { K I } } } } } }

SKY: unblock { B "x" -> "x" { "y" -> "y" } }

SKY: unquote { letrec "unquote"
               { B "x1" -> "x1"
                 { "y" "x2" -> { { "unquote" "y" } { "unquote" "x2" } }
                   { "z" -> "z" } } } }
SKY: true { K }
SKY: false { K I }

SKY: isquote { letrec "isquote"
               { B { "x1" "y" } -> false
                 { B "x2" -> true
                   { "x3" "y3" -> { { "isquote" "x3" } { "isquote" "y3" } { K I } }
                     { "x4" -> false } } } } }

SKY: quote { letrec "quote"
             { L "x"
               { F "x" { B "x" }
                 { L "p" { L "q" { { "quote" "p" } { "quote" "q" } } } } }
             } }

DEFER: enact
SKY: evalop { "x" -> { unblock { enact "x" } } }

SKY: evaloplet { let "unblock" { B "x" -> "x" I } {
                     "x" -> { "unblock" { "enact" "x" } }
                 } }

SKY: enact1 {
    B Y "x1" -> { "enact" { "x1" { B Y "x1" } } }
    { B K "x2" "x1" -> { "enact" { K "x2" "x1" } }
      { B S "x3" "x2" "x1" -> { "enact" { S "x3" "x2" "x1" } }
        { B F "x3" "x2" "x1" -> { "enact" { F { "evalop" "x3" } "x2" "x1" } }
          { B B "x4" "x3" "x2" "x1" -> { B B "x4" "x3" "x2" "x1" }
            { B "x5" "x4" "x3" "x2" "x1" ->
              { "enact" { "x5" { "evalop" "x4" } { "evalop" "x3" } "x2" "x1" } }
              { "x1" -> "x1" } } } } } } }

! Enact
SKY: enact { letrec "enact" {
                 let "unblock" { B "x" -> "x" I } {
                     let "evalop" { "x" -> { "unblock" { "enact" "x" } } } {
                         let "enact1" {
                             B Y "x1" -> { "enact" { "x1" { B Y "x1" } } }
                             { B K "x2" "x1" -> { "enact" { K "x2" "x1" } }
                               { B S "x3" "x2" "x1" -> { "enact" { S "x3" "x2" "x1" } }
                                 { B F "x3" "x2" "x1" -> { "enact" { F { "evalop" "x3" } "x2" "x1" } }
                                   { B B "x4" "x3" "x2" "x1" -> { B B "x4" "x3" "x2" "x1" }
                                     { B "x5" "x4" "x3" "x2" "x1" ->
                                       { "enact" { "x5" { "evalop" "x4" } { "evalop" "x3" } "x2" "x1" } }
                                       { "x1" -> "x1" } } } } } } } {
                             "x2" "x1" -> { "enact1" { "enact" "x2" "x1" } }
                             { "x1" -> "x1" } } } } } }

! SKY: sky-dup { letrec "dup"
!                { B "x" -> { B "x" { B "x" } }
!                  { B "y" { B "z" } ->
!                    { B "y" { B "dup" } }
!                    { "_" -> error }}  } }
! SKY: sky-dup { QQ{ "x" "y" } -> QQ{ "x" "x" "y" }
! SKY: sky-dup { { pair "x" "y" } -> { pair "x" { pair "x" { "y" } }
SKY: sky-dup { { { B "x" { B "y" "z" } } -> { B "x" { B "x" { B "y" "z" } } }
               ! { QQ{ "x2" f } -> QQ{ "x2" "x2" }
               ! { { B "y" "z" } -> { B "y" "y" "z" }
                                     { "_" -> "error" } } }

! SKY: sky-push { {  } }

SYNTAX: SE{ (parse-skyfeb-literal) skyfeb-reduce suffix! ;

! SKY: if-op { L "then" { L "else" { L "thing" { F { "thing" } "then" "else" } } } }

! SKY: sky-cons { L "x" { L "y" { B "x" { B "y" } } } }

! SKY: quote { letrec "quote"
!                { L "obj" { F
!                            "obj"
!                            { B "obj" }
!                            { L "s" { L "t" { sky-cons { "quote" "s" } { "quote" "t" } } } }
!                            ! { { L "s" { L "t" { sky-cons "s" "t" } } } }
!                            ! "obj"
!                          } } }

! SKY: dup-test { L ""
