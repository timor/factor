USING: accessors arrays assocs classes classes.algebra combinators
combinators.short-circuit effects fmc fmc.states kernel make quotations
sequences strings typed words ;

IN: fmc.builder

TYPED: loc, ( term: fmc-seq loc: fmc-loc -- )
    <loc-push> , ;
! Specify actions per location
! alist of : { loc [  ]( obj -- term: fmc-seq ) }

: expect ( type type -- )
    2dup classes-intersect? [ 2drop ]
    [ "declaration error" 3array throw ] if ;

GENERIC: make-fmc* ( word -- )
TYPED: make-fmc ( quot: callable -- term: fmc-seq )
    [ [ make-fmc* ] each ] { } make ;

GENERIC: fmc-type-term ( word -- )
M: object fmc-type-term
    class-of <const> +tau+ loc, ;

! e.g.: fixnum+ ( x: fixnum y: fixnum -- z: integer )
! → [ fixnum expect fixnum expect integer ]τ
TYPED: effect-type-term ( effect: effect -- )
    [ effect-in-types <reversed> [ \ expect [ <fmc-prim> ] bi@ 2array ]
      map concat +tau+ loc,
    ] [ effect-out-types [ <fmc-prim> ] map +tau+ loc, ] bi ;

! M: word fmc-type-term
!     stack-effect effect-type-term ;

GENERIC: fmc-code-term ( word -- )
M: object fmc-code-term <const> +psi+ loc, ;
! M: word fmc-code-term <const> +psi+ loc, ;

M: object make-fmc* <fmc-prim> , ;
    ! fmc-code-term ;
    ! [ fmc-code-term ]
    ! [ fmc-type-term ] bi ;

! var names: { name-var type-var type }
PREDICATE: var-list < sequence
    [ { [ length 3 = ]
        [ first varname? ]
        [ second varname? ]
        [ third classoid? ] } 1&& ] all? ;

TYPED: elements>vars ( elts default: string -- seq: var-list )
    '[
        [ effect>name _ or [ <uvar> ] [ "_t" append <uvar> ] bi ]
        [ effect>type ] bi 3array
    ] map ;

GENERIC: in/out-types ( word -- in-types: var-list out-types: var-list )

TYPED: effect>vars ( effect: effect -- in-types: var-list out-types: var-list )
    [ in>> "in" elements>vars ]
    [ out>> "out" elements>vars ] bi ;

M: typed-word in/out-types stack-effect
    effect>vars ;
    ! [ effect-in-types ]
    ! [ effect-out-types ] bi ;

M: word in/out-types
    dup stack-effect [
        [ nip effect-in-names ]
        [ { [ drop "input-classes" word-prop ] [ nip in>> length object <repetition> ] } 2|| ] 2bi
      zip
    ] [ [ nip effect-out-names ]
      [ { [ drop "default-output-classes" word-prop ] [ nip out>> length object <repetition> ] } 2|| ] 2bi
      zip
    ] 2bi <effect> effect>vars ;

    ! [ stack-effect ] keep

    ! [ { [ nip "default-output-classes" word-prop ] [ drop out>> length object <repetition> ] } 2|| ]
    ! 2bi ;

! : in/out-var/types ( word -- in-type-vars out-type-vars )
!     [ stack-effect effect-in-names [ "in" or ] map ]
!     [ stack-effect effect-out-names [ "out" or ] map ]
!     [ in/out-types ] tri
!     swapd [ <zipped> ] 2bi@ ;

TYPED: word-consumption ( in-type-vars: var-list -- )
    <reversed> [| | first2 :> ( var type-var )
                var f <loc-pop> ,
                type-var +tau+ <loc-pop> ,
    ] each ;

TYPED: in-type-check ( in-type-vars: var-list -- )
    [| | rest-slice first2 :> ( type-var type )
     type-var f <loc-push> ,
     type <fmc-prim> , \ expect <fmc-prim> ,
    ] each ;


TYPED: prim-execution ( word: word in-type-vars: var-list -- )
    [ first f <loc-push> ] map swap <fmc-prim> suffix +psi+ loc, ;

TYPED: word-production ( out-type-vars: var-list -- )
    [ third <fmc-prim> ] map +tau+ loc, ;

! : types-consumption ( in-type-vars -- )
!     <reversed> [| var type |
!                 var [ +tau+ <loc-pop> , ] [ f <loc-push> , ] bi
!                 type <const> f <loc-push> , \ expect <fmc-prim> ,
!     ] assoc-each ;

! : types-production ( out-type-vars -- )
!     values [ <fmc-prim> ] map +tau+ loc, ;

! : word-type-term ( word -- )
!     in/out-var/types
!     [ types-consumption ]
!     [ types-production ] bi* ;
    ! [ effect-in-types <reversed> [ \ expect [ <fmc-prim> ] bi@ 2array ]
    !   map concat +tau+ loc,
    ! ] [ effect-out-types [ <fmc-prim> ] map +tau+ loc, ] bi ;
    ! [ effect-in-names [ "in" or "_t" append <uvar> ] map ]
    ! [ effect-in-types <reversed> ] bi
    ! [  ]
    ! [  ] 2bi ;

! : exec-fmc ( word -- )
!     dup stack-effect effect-in-names
!     [ "in" or <uvar> ] map
!     [ <reversed> [ f <loc-pop> ] map ]
!     [ [ f <loc-push> ] map ] bi append swap <fmc-prim> suffix +psi+ loc, ;

! : word-code-term ( word -- )
!     dup stack-effect effect-in-names
!     [ "in" or <uvar> ] map
!     [ <reversed> [ f <loc-pop> ] map % ]
!     [ [ f <loc-push> ] map swap <fmc-prim> suffix +psi+ loc, ] bi ;


: exec-fmc ( word -- )
    dup in/out-types
    {
        [ drop nip word-consumption ]
        [ drop nip in-type-check ]
        [ drop prim-execution ]
        [ 2nip word-production  ]
    }
    3cleave ;
    ! [ word-code-term ] [ word-type-term ] bi ;

: make-all-shuffles ( word -- )
    { f +tau+ } shuffle>fmc % ;
!     "shuffle" word-prop
!     [ in>> ] [ out>> ] bi uvar-shuffle
!     [ [ <varname> ] map ] bi@
!     { f +tau+ } [ loc-shuffle>fmc % ] 2with each ;

: make-word-fmc ( word -- )
    { { [ dup shuffle-word? ] [ make-all-shuffles ] }
      [ exec-fmc ]
    } cond ;

M: word make-fmc* make-word-fmc ;

! Only type of argument of interest?

! M: \ ? make-fmc* drop
!     [let
!         "else" <uvar> dup :> else +psi+ <loc-pop>
!         "then" <uvar> dup :> then +psi+ <loc-pop>
!         "_" <uvar> +psi+ <loc-pop>
!         "?" <uvar> dup :> c +tau+ <loc-pop>
!         { POSTPONE: f class= } <fmc-prim> map c prefix

!     ]

: expand-fmc ( word -- trace )
    make-fmc seq>proper beta init-fmc-state run-fmc ;
