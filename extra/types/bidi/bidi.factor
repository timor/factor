USING: accessors arrays classes classes.algebra compiler.utilities continuations
effects kernel namespaces quotations sequences types words ;

IN: types.bidi

! * Admitting sets of types on the stack
! This represents the variance directly
: trace-and ( value-set type2 -- value-set )
    over classoid?
    [ class-and ]
    [ 2dup instance?
      [ drop ]
      [ 2drop null ] if ] if ;

! * Bidirectional ping/pong inference

! Turn words into eval step tuples as we move from left to right.
! eval steps a

GENERIC: apply* ( before-stack word -- after-stack )
GENERIC: reverse ( before-stack word -- quotation )

! These are used to pre-filter
GENERIC: in-types ( word -- seq )
GENERIC: out-types ( word -- seq )
M: word in-types
    [ stack-effect effect-in-types ] keep
    "input-classes" word-prop
    [ [ class-and ] 2map ] when*
    ;
M: \ call in-types drop
    { callable } ;
M: word out-types
    [ stack-effect effect-out-types ] keep
    "default-output-classes" word-prop
    [ [ class-and ] 2map ] when* ;

M: object in-types drop f ;
! M: object out-types type-of 1array ;
M: object out-types 1array ;

: pad-head-shorter ( seq seq elt -- seq seq )
    [ [ <reversed> ] bi@ ] dip pad-tail-shorter [ <reversed> ] bi@ ;

: pad-typestack ( typestack input-types -- typestack input-types )
    object pad-head-shorter ;

: apply-in-types ( typestack word -- typestack )
    in-types pad-typestack
    [ trace-and ] 2map ;

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

: apply-word-effect ( before-stack word -- after-stack )
    [ in-types length head* ]
    [ out-types append ] bi ;

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
TUPLE: eval-state word inputs outputs future history ;

: <begin-eval> ( code -- obj )
    eval-state new
    swap >>future ;

: last-outputs ( eval-state -- seq )
    history>> dup [ outputs>> ] when ;

: step-end? ( eval-state -- ? )
    future>> empty? ;

GENERIC: constrain-inputs ( inputs word -- inputs )
M: object constrain-inputs
    apply-in-types ;
GENERIC: calculate-outputs ( inputs word -- outputs )
M: object calculate-outputs
    nip out-types ;
PREDICATE: shuffle-word < word "shuffle" word-prop >boolean ;
M: shuffle calculate-outputs
    "shuffle" word-prop shuffle ;

! \

ERROR: empty-inputs inputs word ;
: step ( eval-state -- eval-state keep-going? )
    [let :> s
     s step-end?
     [ s f ]
     [
         s future>> unclip :> ( rest word )
         word inline?
         [ s [ word def>> prepose ] change-future step ]
         [
             s last-outputs :> inputs
             inputs word constrain-inputs :> new-inputs
             new-inputs [ null = ] any? [ new-inputs word empty-inputs ] when
             new-inputs word calculate-outputs :> outputs
             eval-state new
             word >>word
             new-inputs >>inputs
             outputs >>outputs
             s >>history
             rest >>future
             t
         ] if
     ] if
    ] ;

: step-back ( eval-state -- eval-state keep-going? )
    [let :> s
     s
    ] ;

: run ( quot -- eval-state )
    <begin-eval> [ step ] loop ;
