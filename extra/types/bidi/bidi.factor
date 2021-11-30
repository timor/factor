USING: accessors arrays assocs classes classes.algebra combinators
combinators.short-circuit compiler.utilities continuations effects kernel kernel.private
layouts math math.intervals namespaces quotations sequences stack-checker types
types.parametric.effects types.parametric.intervals types.parametric.literal
words ;

IN: types.bidi

! * Gradual typing semantics
! This is the unknown type.  It is only defined for gradual matching, and cannot
! be used to perform comparison.
SINGLETON: ??

! * Admitting sets of types on the stack
! This represents the variance directly
! NOTE: not using, using literal types because otherwise we need to define a new
! union type that can hold values
: effect-and ( value-set effect -- value-set )
    { { [ over effect? ] [ 2dup effect<= ] }
      { [ over quotation? ] [ [ [ infer ] dip 2dup effect<= ] ] }
      [ f ]
    } cond
    [ drop ] [ 2drop null ] if ;

: trace-and ( value-set type2 -- value-set )
    {
        { [ dup ??? ] [ drop ] }
        { [ over ??? ] [ nip ] }
        { [ over classoid? ] [ class-and ] }
        { [ dup effect? ] [ effect-and ] }
        { [ dup classoid? ] [ 2dup instance? [ drop ] [ 2drop null ] if ] }
        ! NOTE: this should never be called if we are working on type level!
        ! [ 2dup =
        !   [ drop ]
        !   [ 2drop null ] if
        ! ]
    } cond ;

! * Bidirectional ping/pong inference

! Turn words into eval step tuples as we move from left to right.
! eval steps a

GENERIC: apply* ( before-stack word -- after-stack )
GENERIC: type-inverse ( before-stack word -- quotation )
M: \ drop type-inverse drop
    last 1quotation ;
M: \ nip type-inverse drop
    [ length 2 - ] keep nth [ swap ] curry ;
M: \ dup type-inverse drop
    drop [ trace-and ] ;
M: \ swap type-inverse drop
    drop [ swap ] ;
M: configuration type-inverse 2drop [ ] ;
M: \ declare type-inverse 2drop [ ] ;
    ! last 1quotation ;
M: word type-inverse "undefined type-inverse" 2array throw ;
: value-inverse ( before-stack obj -- quotation )
    nip
    f swap 2array 1array <configuration> [ drop ] curry ;
! nip 1array [ declare drop ] curry ;

M: object type-inverse
    <literal-type> value-inverse ;
M: type type-inverse
    value-inverse ;

! These are used to convert stack element types into a form where we can perform
! type computation on.
GENERIC: effect>gtype ( obj -- type )
: effect-types>gtype ( seq -- seq )
    [ dup pair? [ first2 effect>gtype 2array ] when ] map ;

M: effect effect>gtype
    dup bivariable-effect?
    [ drop callable ]
    [ {
        [ in-var>> ]
        [ in>> effect-types>gtype ]
        [ out-var>> ]
        [ out>> effect-types>gtype ]
    } cleave <variable-effect> <typed-quotation> ] if ;
M: configuration effect>gtype
    elements>> effect-types>gtype <configuration> ;
M: object effect>gtype <literal-type> ;
M: type effect>gtype ;
M: \ fixnum effect>gtype drop
    fixnum most-negative-fixnum most-positive-fixnum [a,b] <interval-type> ;
! TODO: This should probably be an ad-hoc conversion at call-sites!
M: class effect>gtype
    dup real class<=
    [ [-inf,inf] <interval-type> ] when ;

! These are used to pre-filter
GENERIC: in-types* ( word -- seq )
GENERIC: out-types* ( word -- seq )
: in-types ( word -- seq )
    in-types* [ effect>gtype ] map ;
: out-types ( word -- seq )
    out-types* [ effect>gtype ] map ;

: effect-type-raw ( obj -- type )
    dup pair? [ second ] [ drop object ] if ;
: raw-in-types ( effect -- types )
    in>> [ effect-type-raw ] map ;
: raw-out-types ( effect -- types )
    out>> [ effect-type-raw ] map ;
M: effect in-types* raw-in-types ;
M: effect out-types* raw-out-types ;
M: word in-types*
    [ stack-effect raw-in-types ] keep
    "input-classes" word-prop
    [ [ class-and ] 2map ] when*
    ;
M: \ call in-types* drop
    { callable } ;
M: word out-types*
    [ stack-effect effect-out-types ] keep
    "default-output-classes" word-prop
    [ [ class-and ] 2map ] when* ;

! Since we use configurations as declarations, the input types only affect the
! effect depth
: types>configuration ( types -- obj )
    [ f swap 2array ] map <configuration> ;

: configuration>types ( configuration -- types )
    elements>> [ dup pair? [ second ] [ drop object ] if ] map ;

M: configuration in-types* elements>> length object <repetition> ;

M: configuration out-types* configuration>types ;

M: object in-types* drop f ;
! M: object out-types* type-of 1array ;
M: object out-types* <literal-type> 1array ;

: pad-head-shorter ( seq seq elt -- seq seq )
    [ [ <reversed> ] bi@ ] dip pad-tail-shorter [ <reversed> ] bi@ ;

: pad-typestack ( typestack input-types -- typestack input-types )
    ?? pad-head-shorter ;

: apply-types ( typestack types -- typestack )
    pad-typestack
    [ trace-and ] 2map ;

: apply-in-types ( typestack word -- typestack )
    in-types apply-types ;

! * Tracing
SYMBOL: last-stack
SYMBOL: undos

: apply ( before-stack word -- after-stack )
    [ apply-in-types
      dup last-stack set ]
    [
        dup inline?
        [ def>> [ apply ] each ]
        [
            [ undos [ swap prefix ] change ]
            [ apply* ] bi
        ] if
    ] bi ;

M: object apply*
    suffix ;

GENERIC: apply-word-effect ( before-stack word -- after-stack )

M: word apply-word-effect
    [ in-types length head* ]
    [ out-types append ] bi ;
M: configuration apply-word-effect
    M\ word apply-word-effect execute ;
M: type apply-word-effect
    suffix ;
M: object apply-word-effect
    suffix ;

ERROR: fold-failed preceding-error ;
: fold-application ( before-stack word -- after-stack )
    [ 1quotation with-datastack ] [ fold-failed ] recover ;

M: word apply*
    dup "shuffle" word-prop
    [ nip shuffle ]
    [
        dup foldable?
        [ [ fold-application ] [ dup fold-failed? [ drop apply-word-effect ]
                                 [ rethrow ] if ] recover ]
        [ apply-word-effect ] if
    ] if* ;

M: \ call apply* drop
    unclip-last dup callable?
    [ [ apply ] each ] [ 2drop { } ] if ;

M: \ dip apply* drop
    2 cut* first2 swap
    [ suffix \ call apply* ] dip
    suffix ;

! TODO: could have warning here why fold failed!
: fold-accept-error ( before-stack word -- after-stack )
    [ fold-application ] [ dup fold-failed? [ 3drop { } ] [ rethrow ] if ] recover ;
M: \ curry apply* fold-accept-error ;
M: \ compose apply* fold-accept-error ;

! : run ( quot -- penultimate-stack last-stack undos )
!     f last-stack set
!     [ ] undos set
!     { } swap [ apply ] each last-stack get swap undos get ;

! * Linked eval states
! Typed quotations: associate an instantiated function type to each function
! term as we are going left to right.

! Look up the function type for each word recursively, apply

! Primitive combinator base: if

GENERIC: definition ( obj -- quot/f )
! M: object definition drop f ;
! This should create an invariant call which is inversible per default
M: object definition drop f ;
M: type definition drop f ;

PREDICATE: special-word < word { ? drop swap dup declare call } member? ;
PREDICATE: nodef-word < word def>> not ;
PREDICATE: recursive-base-word < word [ 1quotation ] [ def>> ] bi = ;
UNION: base-word special-word nodef-word recursive-base-word ;
M: base-word definition drop f ;
PREDICATE: non-special-word < word { [ base-word? not ] [ type? not ] } 1&& ;
PREDICATE: inline-word < non-special-word inline? ;
! { [ base-word? not ] [ type? not ] [ inline? ] } 1&& ;
M: inline-word definition def>> ;
M: \ if definition def>> ;

PREDICATE: normal-word < non-special-word inline? not ;

: word>declare-quot ( word -- quot )
    in-types
    [ [  ] ]
    [ types>configuration 1quotation ] if-empty ;
M: normal-word definition
    [ word>declare-quot ]
    [ in-types
      [ [  ] ]
      [
        length [ [ drop ] ] replicate [ ] [ compose ] map-reduce
      ] if-empty compose
    ] [
        out-types >quotation compose
    ] tri ;

PREDICATE: shuffle-word < word "shuffle" word-prop >boolean ;
! This is the word which performs the actual dependent effect type
! calculations.  Regular words operate element-wise, while e.g. shuffle words
! actually swap type elements.
GENERIC: map-type ( stack obj -- stack )
! M: base-word map-type
!     "undefined" 2array throw ;
M: \ drop map-type drop
    but-last ;
M: \ dup map-type drop
    dup last suffix ;
M: object map-type ( stack w -- stack )
    ! stack-in w apply-word-effect :> stack-out
    ! stack-out stack-in stack-out [ >array ] bi@ <effect> ;
    apply-word-effect ;
M: shuffle-word map-type
    ! [ <reversed> ] dip
    "shuffle" word-prop shuffle ;
    ! reverse ;

! NOTE: the type-inverse of a declare is pushing it's spec, This is the point where
! we actually propagate type-information backwards
ERROR: declared-null-value stack ;
PREDICATE: declaration < array ;
: apply-input-types/check ( stack types -- stack )
    apply-types dup [ null = ] any? [ declared-null-value ] when ;

M: \ declare map-type drop
    ! Compile-time literal check!
    unclip-last declaration check-instance
    apply-input-types/check
    ;

M: configuration map-type
    configuration>types apply-input-types/check ;
    ! out-types append ;

DEFER: map-types
: map-dispatch-branch ( stack types quot  -- stack trace )
    [ clone ] [ apply-types ] [ map-types ] tri* ;

: filter-dispatch ( stacks-and-traces -- stacks-and-traces )
    [ first [ null = ] any? ] reject ;
! Intersection of arrows type semantics.
! Return entry of form
! { dispatch { spec trace } ... }
ERROR: no-matching-dispatch ;
ERROR: incompatible-inputs inputs word ;

: map-dispatch ( stack dispatch-pairs -- trace-elt stack )
    [ first2 [ map-dispatch-branch 2array ] [ dup incompatible-inputs?
                                              [ 4drop f ]
                                              [ rethrow ] if
                                            ] recover
    ] with map ! :> { { stack1 trace1 } ... }
    ! filter-dispatch
    sift dup empty? [ no-matching-dispatch ] when
    unzip "dispatch" prefix swap
    [ ] [ [ class-or ] 2map ] map-reduce ;


: map-if ( stack -- trace-elt stack )
    2 cut* first2
    [let
     ! Here we actually check for an instance because these must be literal
     [ callable check-instance [ drop ] prepose ] bi@
     :> ( then else )
     f class-of 1array else 2array
     f class-of class-not 1array then 2array
     2array map-dispatch
     ! [ map-dispatch ]
     ! [ \ if prefix swap ] bi swap
    ] ;

! M: \ call map-type ( stack w -- stack )
!     drop
!     unclip-last dup callable? [
!     ]
!     [ suffix \ call apply-word-effect ] if ;

GENERIC: constrain-inputs ( inputs word -- inputs )
! NOTE: only doing length here!
M: object constrain-inputs
    in-types length ?? <repetition> apply-types ;
    ! apply-in-types ;

: <type-effect> ( in-types out-types -- effect )
    [ [ f swap 2array ] map ] bi@
    <effect> ;


SYMBOL: inline-call-stack
:: map-types ( stack quot -- stack trace )
    stack quot >quotation [| stack w |
                stack w constrain-inputs :> stack-in
                stack-in [ null = ] any? [ stack w incompatible-inputs ] when
                w definition
                [| def | inline-call-stack get w suffix
                 inline-call-stack
                 [
                     stack-in def map-types
                 ] with-variable
                 w prefix
                ]
                [
                    w \ if eq?
                    [ stack-in [ map-if tuck ] keep swap <type-effect> 2array ]
                    [ stack-in w map-type stack-in over [ >array ] bi@ <type-effect>
                      w swap 2array
                    ] if
                ] if*
    ] { } map-as ;

: inverse-type-quot ( trace -- quotation )
    [ ] swap
    <reversed>
    [ dup second effect?
      [ first2 in-types swap type-inverse compose ]
      [ rest inverse-type-quot compose ] if
    ] each ;

! Helper
: type. ( quot -- )
    f swap map-types . . ;

: infer-type ( quot -- effect )
    f swap map-types
    [ inverse-type-quot map-types drop ] keepd <type-effect> ;

! : <begin-eval> ( code -- obj )
!     eval-state new
!     swap >>future ;

! : last-outputs ( eval-state -- seq )
!     history>> dup [ outputs>> ] when ;

! : step-end? ( eval-state -- ? )
!     future>> empty? ;

! GENERIC: calculate-outputs ( inputs word -- outputs )
! M: object calculate-outputs
!     nip out-types* ;
! PREDICATE: shuffle-word < word "shuffle" word-prop >boolean ;
! M: shuffle calculate-outputs
!     "shuffle" word-prop shuffle ;

! ! \

! ERROR: empty-inputs inputs word ;
! : step ( eval-state -- eval-state keep-going? )
!     [let :> s
!      s step-end?
!      [ s f ]
!      [
!          s future>> unclip :> ( rest word )
!          word inline?
!          [ s [ word def>> prepose ] change-future step ]
!          [
!              s last-outputs :> inputs
!              inputs word constrain-inputs :> new-inputs
!              new-inputs [ null = ] any? [ new-inputs word empty-inputs ] when
!              new-inputs word calculate-outputs :> outputs
!              eval-state new
!              word >>word
!              new-inputs >>inputs
!              outputs >>outputs
!              s >>history
!              rest >>future
!              t
!          ] if
!      ] if
!     ] ;

! : step-back ( eval-state -- eval-state keep-going? )
!     [let :> s
!      s
!     ] ;

! : run ( quot -- eval-state )
!     <begin-eval> [ step ] loop ;
