USING: accessors arrays assocs classes classes.algebra classes.algebra.private
combinators combinators.short-circuit compiler.utilities continuations effects
kernel kernel.private math math.combinatorics namespaces prettyprint quotations
sequences types types.parametric.effects types.protocols words ;

IN: types.bidi

! * Gradual typing semantics
! This is the unknown type.  It is only defined for gradual matching, and cannot
! be used to perform comparison.
! Currently, it cannot be used for class algebra, because its interpretation as
! value set must be made explicit.  This is the task of the trace-and/trace-or words.
: class\ ( class1 class2 -- class )
    class-not class-and ;
! SYMBOL: ??
! : ??? ( obj -- ? ) ?? eq? ;

! * Admitting sets of types on the stack
! TODO: actual type containment?  This right now is only intended and called for
! out→in contexts..
! NOTE: Intersection of variable effects can only be a variable effect if both
! have been variable...
! Variance: ( x -- x ) < ( ..a x -- ..a x ) < ( ..a x -- ..b x )
! Intersections: ( x -- x ) ( x -- x x ) = null
! The more parameters are specified in the input, the more specific the effect is
! The more unspecified parameter
! The

: effect-and ( effect effect -- value-set )
    over bivariable-effect? [ swap ] when
    {
      { [ over effect? ] [ 2dup effect<= ] }
      ! { [ over quotation? ] [ [ [ infer ] dip 2dup effect<= ] ] }
        ! { [ over bivariable-effect? ] [  ] }
        ! { [ dup [ bivariable-effect? ] ] [ [ type>classoid ] class-and ] }
      [ f ]
    } cond
    [ drop ] [ 2drop null ] if ;

! Gradual types
: trace-and ( value-set type2 -- value-set )
    {
        { [ dup ??? ] [ drop ] }
        { [ over ??? ] [ nip ] }
        { [ dup classoid? ] [ [ type>classoid ] dip class-and ] }
        { [ dup effect? ] [ [ type>effect ] dip effect-and ] }
        ! { [ dup classoid? ] [ 2dup instance? [ drop ] [ 2drop null ] if ] }
        ! NOTE: this should never be called if we are working on type level!
        ! NOTENOTE: but we are not, we are working on value set level!
        [ 2dup =
          [ drop ]
          [ 2drop null ] if
        ]
    } cond ;

! TUPLE: trace-union members ;
GENERIC: unknown? ( gtype -- ? )
M: ?? unknown? drop t ;
! M: trace-union unknown?
!     members>> [ unknown? ] any? ;
M: object unknown? drop f ;
M: anonymous-union unknown?
    members>> [ unknown? ] any? ;
M: anonymous-intersection unknown?
    participants>> [ unknown? ] any? ;


! Used when we need to compare on value set level
GENERIC: concretize ( gtype -- class )
M: ?? concretize drop union{ object null } ;
M: classoid concretize ;
! M: trace-union concretize
!     members>> [ concretize ] map <anonymous-union> ;

! NOTE: this is not strictly a concretization of a gradual type, but serves to
! be able to employ the underlying class algebra system even for values, which
! represent the type that only contains that value, e.g. an anonymous equality
! predicate.
! M: object concretize <literal-type> ;

M: anonymous-union concretize
    members>> [ concretize ] map <anonymous-union> ;
M: anonymous-intersection concretize
    participants>> [ concretize ] map <anonymous-intersection> ;
! M: object concretize ;
! Gradual types
! This is used to compute element-wise unions that can be used on the type stack
: trace-or ( value-set type2 -- value-set )
    {
        { [ 2dup = ] [ drop ] }
        { [ 2dup [ type? ] both? ] [ class-or ] }
      !   { [ 2dup [ type? not ] both? ] [ 2drop null ] }
      !   { [ 2dup [ unknown? ] either? ] [ 2array trace-union boa ] }
      ! { [ 2dup [ classoid? ] both? ] [ class-or ] }
      ! [ [ dup type? [ <wrapper> ] unless ] bi@ class-or ]
    } cond ;
    ! class-or ;

    ! For primitive parallel constructs, we must ensure that only one path is taken
    ! under runtime interpretation.  Possibly expensive.
 : any-intersect? ( classes -- pair/f )
     2 [ first2 classes-intersect? ] find-combination ;

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
M: \ trace-and type-inverse drop
    drop [ dup ] ;
M: \ swap type-inverse drop
    drop [ swap ] ;
M: configuration type-inverse 2drop [ ] ;

! NOTE: the type-inverse of a declare is pushing it's spec so it will be deleted
! by the preceding spec literal.  This differs from using configurations as declaration
! construct because this here has macro semantics due to literal inputs on the stack.
M: \ declare type-inverse drop
     last 1quotation ;

: types>declaration ( types -- quot )
    >array [ declare ] curry ;

M: word type-inverse "undefined type-inverse" 2array throw ;
: value-inverse ( before-stack obj -- quotation )
    nip 1array types>declaration [ drop ] compose ;
    ! f swap 2array 1array <configuration> [ drop ] curry ;
! nip 1array [ declare drop ] curry ;

M: object type-inverse
    <wrapper> value-inverse ;
    ! <literal-type> value-inverse ;
M: type type-inverse
    value-inverse ;

ERROR: literal-type-expected type ;
: literal>value ( type -- value )
    dup wrapper? [ literal-type-expected ] unless
    wrapped>> ;

: test-literal ( type class -- ? )
    over wrapper? [ [ wrapped>> ] dip instance? ]
    [ 2drop f ] if ;

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
M: object effect>gtype ;
M: type effect>gtype ;
! M: \ fixnum effect>gtype drop
!     fixnum most-negative-fixnum most-positive-fixnum [a,b] <interval-type> ;
! TODO: This should probably be an ad-hoc conversion at call-sites!
! M: class effect>gtype
!     dup real class<=
!     [ [-inf,inf] <interval-type> ] when ;

! These are used to pre-filter
GENERIC: in-types* ( word -- seq )
GENERIC: out-types* ( word -- seq )
: in-types ( word -- seq )
    in-types* ! [ effect>gtype ] map >array
    ;
: out-types ( word -- seq )
    out-types* ! [ effect>gtype ] map >array
    ;

: effect-type-raw ( obj -- type )
    dup pair? [ second ] [ drop ?? ] if ;
: raw-in-types ( effect -- types )
    in>> [ effect-type-raw ] map ;
: raw-out-types ( effect -- types )
    out>> [ effect-type-raw ] map ;
M: effect in-types* raw-in-types ;
M: effect out-types* raw-out-types ;
M: word in-types*
    [ stack-effect raw-in-types ] keep
    "input-classes" word-prop
    [ [ trace-and ] 2map ] when*
    ;
M: \ call in-types* drop
    { callable } ;
M: word out-types*
    [ stack-effect raw-out-types ] keep
    "default-output-classes" word-prop
    [ [ trace-and ] 2map ] when* ;

! Since we use configurations as declarations, the input types only affect the
! effect depth
! : types>configuration ( types -- obj )
!     [ f swap 2array ] map <configuration> ;

: configuration>types ( configuration -- types )
    elements>> [ dup pair? [ second ] [ drop object ] if ] map ;

M: configuration in-types* elements>> length object <repetition> ;

M: configuration out-types* configuration>types ;

M: object in-types* drop f ;
! M: object out-types* type-of 1array ;
! M: object out-types* <literal-type> 1array ;
M: object out-types* 1array ;

: pad-typestack ( typestack input-types -- typestack input-types )
    ?? pad-head-shorter ;

: apply-types ( typestack types -- typestack )
    pad-typestack
    [ trace-and ] 2map ;

! NOTE: only used in a left-to-right context right now in declarations.  The
! idea is that we carry over unknowns from the left while assuming actual values
! on the right
: apply-concretized-types ( typestack types -- typestack )
    pad-typestack [ concretize ] map [ class-and ] 2map ;

! XXX
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

: apply-static-effect ( before-stack effect -- after-stack )
    { { [ dup terminated?>> ] [ 2drop { ?? } ] }
      { [ dup bivariable-effect? ] [ nip out-types ] }
      [
          [ in-types length head* ]
          [ out-types append ] bi
      ]
    } cond ;

M: word apply-word-effect
     stack-effect apply-static-effect ;
! NOTE: unused until we can execute configurations!
! M: configuration apply-word-effect
!     M\ word apply-word-effect execute ;
M: type apply-word-effect
    suffix ;
M: object apply-word-effect
    <wrapper> suffix ;

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

! NOTE: doing this beforehand because ordering will try to check the predicate
! quotation for wrapper tests, but that fails if the class to check against has
! not been compiled yet
! TODO check if this is needed after implementing lazyness correctly for wrapper
! predicate defs...
<<
PREDICATE: special-word < word { drop swap dup declare call trace-and } member? ;
PREDICATE: nodef-word < word def>> not ;
PREDICATE: recursive-base-word < word [ 1quotation ] [ def>> ] bi = ;
UNION: base-word special-word nodef-word recursive-base-word ;
! M: base-word definition drop f ;
>>
PREDICATE: non-special-word < word { [ base-word? not ] [ type? not ] } 1&& ;
PREDICATE: inline-word < non-special-word inline? ;
! { [ base-word? not ] [ type? not ] [ inline? ] } 1&& ;
M: inline-word definition def>> ;
M: \ if definition def>> ;

PREDICATE: normal-word < non-special-word inline? not ;

: word>declare-quot ( word -- quot )
    in-types
    [ [  ] ]
    [ types>declaration ] if-empty ;
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
! Self-evaluating, basically unconditional folding to ensure that we don't end
! up with lazy nested inference inverses
M: \ trace-and map-type drop
    2 cut* first2 trace-and suffix ;

M: object map-type ( stack w -- stack )
    ! stack-in w apply-word-effect :> stack-out
    ! stack-out stack-in stack-out [ >array ] bi@ <effect> ;
    apply-word-effect ;
: shuffle-stack ( stack effect -- stack )
    shuffle-mapping
    [ supremum 1 + cut* ]
    [ swap nths ] bi append ;
M: shuffle-word map-type
    "shuffle" word-prop shuffle-stack ;
    ! "undefined shuffle" 2array throw ;
    ! ! [ <reversed> ] dip
    ! "shuffle" word-prop shuffle ;
    ! ! reverse ;

ERROR: declared-null-value stack ;
PREDICATE: declaration < wrapper wrapped>> array? ;
: apply-types/check ( stack types -- stack )
    apply-types dup [ null = ] any? [ declared-null-value ] when ;

! NOTE: This word works on the value level.  This means that we concretize the
! type, thus actually performing the assumptions.  If we are presented with an
! unknown type, it should be preserved through the type check
M: \ declare map-type drop
    ! Compile-time literal check!
    unclip-last declaration check-instance
    wrapped>>
    apply-concretized-types
    ;

M: configuration map-type
    configuration>types apply-types/check ;
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

! Singular point for dispatch introduction.
! TODO: this could also be defined on optimizations word property
TUPLE: parallel alternatives ;
C: <parallel> parallel
INSTANCE: parallel type
M: \ ? definition drop
    [
        T{ parallel f {
               [ drop ( :not{ POSTPONE: f } :?? ) nip ]
               [ nip ( :POSTPONE: f :?? ) nip ]
           } }
    ] ;

! TODO: make sure that contagion of ?? is correct
: stack-or ( stack1 stack2 -- stack )
    ?? pad-head-shorter
    [ trace-or ] 2map ;

ERROR: no-applicable-code-path ;
: map-type-parallel ( stack parallel -- trace-elt stack )
    alternatives>> [
        map-types 2array
    ] with map
    ! { stack trace } pairs
    unzip swap [ no-applicable-code-path ]
    [ [ ] [ stack-or ] map-reduce ] if-empty
    [ <parallel> ] dip ;


! NOTE: being replaced by lazy dispatch using ?
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

! For call, there are also different cases.  Literal expansion is done in
! definition expansion, which is basically also only an optimization...
! : call ( ..a quot: ( ..a -- ..b ) -- ..b )
! Call: considered inline.  Has to calculate outputs based on inputs and given
! quotation.
! If we have a quotation, we actually run it, and compute the outputs?
! If we only have a type, we apply the type.  That's what we do for now.
M: \ call map-type drop
    unclip-last
    type>effect apply-static-effect ;
    ! unclip-last apply-static-effect ;
! M: \ call definition

GENERIC: constrain-inputs ( inputs word -- inputs )
! NOTE: only doing length here!
M: object constrain-inputs
    in-types length ?? <repetition> apply-types ;
    ! apply-in-types ;

: <type-effect> ( in-types out-types -- effect )
    [ [ f swap 2array ] map ] bi@
    <effect> ;
! DEFER: trace
! CONSTANT: trace-seq $[ sequence trace <sequence-type> ]
! VARIANT: trace
!     opaque: { word effect }
!     inline: { word { body trace-seq } }
!     parallel: { word { cases } }
! Valid records in the trace language:
! { word ( ?? → ?? ) } opaque call
! { word records... } substituted inline definition
! { parallel( traces ) union-effect } disjoint union execution
! NOTE: union effects are element-wise on input and output effect elements.
! This represents a convex cover of input/output behavior, and can be used for
! applying input types to simplify ruling out possible alternatives:  If two convex
! covers don't overlap, than there is no possiblity for any of its member sets
! to overlap either

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
                    w parallel? [
                        stack-in w map-type-parallel :> ( elt stack-out )
                        stack-out elt stack-in stack-out <type-effect> 2array
                        ! [ w map-type-parallel ] keep swap <type-effect> w swap 2array
                        ! stack-in [ map-if tuck ] keep swap <type-effect> 2array
                    ]
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
    f swap map-types [ . . ] keep
    inverse-type-quot .
    ;

! : infer-type ( quot -- effect )
!     f swap map-types
!     [ inverse-type-quot map-types drop ] keepd <type-effect> ;

! M: callable type-of infer-type ;
