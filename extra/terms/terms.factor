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
: map-args ( term quot: ( subterm -- subterm' ) -- term' )
    over constant-term?
    [ drop ]
    [ [ [ args>> ] dip map  ]
      [ drop from-args* ] 2bi ] if ; inline

ERROR: term-var-has-no-args term-var ;
M: term-var args>> term-var-has-no-args ;

! Check for free occurrences
GENERIC: occurs? ( term-var term -- ? )
M: term-var occurs? = ;
M: proper-term occurs?
    args>> [ occurs? ] with any? ;

! Substitution
GENERIC: lift* ( subst term -- term )
M: term-var lift* { [ of ] [ nip ] } 2|| ;

M: constant-term lift* nip ;
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
