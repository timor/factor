USING: accessors arrays assocs classes classes.algebra effects kernel math
sequences sets words ;

IN: generic.multi


! * Chen & Turau's Dispatch Automaton
! Based on "Multiple-Dispatching Based on Automata".

: method-types ( method -- seq )
    "method-effect" word-prop effect-in-types ;

! * LUA Construction
! M : Confusable set of Methods
! R_k = R(t1, ..., tk ) : Precedence order of the Methods in M, sequence of sequences of methods


TUPLE: state pord next ;

: <state> ( pord -- obj ) state new swap >>pord ;

! domain(R)
: domain ( pord -- methods )
    union-all members ; ! TODO: order important? shouldnt be...

! T_(k)(m)
: arg-type-at ( k method -- type )
    method-types nth ;

! T_(k)(M')
: arg-types-at ( k methods -- types )
    [ arg-type-at ] with map ;

! inverse of T_(k)(M')
: methods-at-type ( type k methods -- methods )
    [ arg-type-at = ] 2with filter ;

! ! GLB(s, t, T) s, t types, T type subset
! : glb ( s t -- seq )
GENERIC: immediate-subtypes ( type -- types )
M: union-class immediate-subtypes class-members ;
M: tuple-class immediate-subtypes class-usage ;

! closure(S)
: subtype-closure ( types -- types )
    [ immediate-subtypes ] gather ;

! : subtype-closure ( types -- types )
!     [ class-usages ] gather ;

! A Π B
: product ( pord pord -- pord )
    [ intersect ] cartesian-map concat harvest ;

! Compute type precedence list over S for t
: type-precedence-list ( type types -- types )
    [ class<= ] with filter sort-classes ;

! M_(k)(t,S), t type, S set of types ->
! :: pord-at ( type k methods types -- pord )
!     type types type-precedence-list
!     [ k methods methods-at-type ] [ product ] map-reduce ;

! M_(k)(t,S), t type, S set of types ->
! :: pord-at ( type k methods types -- pord )
: pord-at ( k methods type types -- pord )
    type-precedence-list
    [ methods-at-type ] 2curry [ product ] map-reduce ;

! is_equal(pord1, pord2)
: pord= ( pord pord -- ? ) = ;

! build_next_states
:: build-next-states ( methods k n state next-states -- )
    state pord>> domain k swap arg-types-at :> types
    types subtype-closure
    [| type | state pord>>
     k methods type types pord-at product
     k n = [ first ] when :> pord
     next-states [ pord>> pord pord= ] find nip
     [ pord <state> [ next-states push ] keep ] unless*
     type state next>> set-at
    ] each ;

! construct
! TODO: implement with accumulate ?
:: construct ( methods n -- states final-states )
    methods <state> 1array :> states!
    states clone :> next-states!
    n [| k |
       V{ } clone :> next-states'
       next-states [| state |
               methods k n state next-states' build-next-states
              ] each
       states next-states' append states!
       next-states next-states!
    ] each-integer
    states next-states ;
