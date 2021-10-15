USING: accessors arrays assocs classes classes.tuple combinators.short-circuit
kernel lists sequences ;

IN: terms

! * Term substituion

MIXIN: term-var
MIXIN: proper-term
UNION: term term-var proper-term ;

PREDICATE: constant-term < proper-term args>> length 0 = ;

! Proper terms must implement this
GENERIC: from-args* ( args exemplar -- term )
SLOT: args
: map-args ( term quot: ( ..a subterm -- ..b subterm' ) -- term' )
    over constant-term?
    [ drop ]
    [ [ [ args>> ] dip map  ]
      [ drop from-args* ] 2bi ] if ; inline

: each-arg ( term quot: ( ..a subterm -- ..b ) -- )
    over constant-term?
    [ 2drop ]
    [ [ args>> ] dip each ] if ; inline

! Can we do that generically?
M: proper-term args>> tuple-slots ;
M: proper-term from-args*
    over empty? [ nip ]
    [ class-of slots>tuple ] if ;

ERROR: term-var-has-no-args term-var ;
M: term-var args>> term-var-has-no-args ;

! Check for _free_ occurrences
GENERIC: occurs-free? ( term-var term -- ? )
M: term-var occurs-free? = ;
M: proper-term occurs-free?
    args>> [ occurs-free? ] with any? ;
GENERIC: occurs-bound? ( term-var term -- ? )
M: term occurs-bound? occurs-free? ;

! Substitution
GENERIC: lift* ( subst term -- term )
M: term-var lift* { [ of ] [ nip ] } 2|| ;

! M: constant-term lift* nip ;
M: proper-term lift*
    [ lift* ] with map-args ;
    ! [ args>> [ lift* ] with map ]
    ! [ from-args* ] bi ;

INSTANCE: list proper-term
M: cons-state args>>
    [ car>> ] [ cdr>> ] bi 2array ;
M: cons-state from-args*
    drop first2 cons ;

ERROR: trying-to-lift-in-end-of-list ;
M: +nil+ lift* trying-to-lift-in-end-of-list ;
M: +nil+ args>> drop f ;
M: +nil+ from-args* 2drop +nil+ ;

GENERIC: term-vars ( term -- seq )
M: term-var term-vars 1array ;
M: proper-term term-vars
    { } clone swap [ term-vars append ] each-arg ;

: var-usage ( term -- counts )
    ! term-vars [ type-var-key ] map histogram ;
    term-vars histogram ;

! In linear terms, there are either 2 occurrences, then it it is a bound
! variable, or there is 1 occurrence, then it is a free variable.
: bound/free-vars ( term -- bound-vars free-vars )
    var-usage [ nip 1 = not ] assoc-partition [ keys ] bi@  ;

! * Simplification protocol
GENERIC: simplify-term* ( term -- changed? term )
M: term-var simplify-term* f swap ;
M: proper-term simplify-term*
    f swap [ simplify-term* [ or ] dip ] map-args ;
: simplify-term ( term -- term )
    [ simplify-term* swap ] loop ;
