USING: accessors arrays assocs combinators.short-circuit kernel lists sequences
;

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
