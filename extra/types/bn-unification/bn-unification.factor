USING: accessors arrays assocs assocs.extras classes combinators
combinators.short-circuit effects hashtables io kernel math math.parser
namespaces sequences sequences.zipped strings words ;

IN: types.bn-unification

TUPLE: varname
    { name string }
    { id integer } ;
C: <varname> varname
TUPLE: rowvarname < varname ;
C: <rowvarname> rowvarname

TUPLE: proper-term
    { symbol }
    { args sequence } ;
C: <proper-term> proper-term

: lcounter ( symbol -- int )
    [ 0 or 1 + dup ] change ;

: with-local-counter ( symbol quot -- )
    [ 0 swap ] dip with-variable ; inline

SYMBOLS: lst nil ;
: cons ( car cdr -- cons )
    2array lst swap <proper-term> ;

! Reverse-mapping
! nil = ( f . f )
ERROR: need-dotted-list ;
:: map>lst ( seq quot: ( x -- y ) -- lst )
    seq empty? [ need-dotted-list
                 ! lst f <proper-term>
    ]
    [
        seq length 1 = [ seq first quot call( x -- y ) ]
        [

            seq unclip-last-slice :> ( rest head )
            head quot call( x -- y ) :> car
            car rest quot map>lst cons
        ] if
    ] if ;

SYMBOLS: -- stk const ;

GENERIC: effect>term ( effect -- term )
M: word effect>term f <proper-term> ;
M: string effect>term \ effect>term lcounter <varname> ;
M: pair effect>term second effect>term ;
: row-term ( name -- term )
    \ effect>term lcounter <rowvarname> ;
M: rowvarname effect>term ;
M: effect effect>term
    [ [ in>> ] [ in-var>> ] bi "r" or row-term prefix ]
    [ [ out>> ] [ out-var>> ] bi "r" or row-term prefix ] bi
    [ [ effect>term ] map>lst 1array stk swap <proper-term> ] bi@
    2array -- swap <proper-term> ;

ERROR: term-mismatch t1 t2 ;
ERROR: recursive-term vname term ;

DEFER: pp
: pp-subst ( subst -- )
    [ [ write " = " write ] [ pp ] bi* ] assoc-each ;

DEFER: elim
: solve ( subst problem -- subst )
    [
        "Solve:" print
        over pp-subst
        unclip-slice first2
        2dup [ pp ] bi@
    { { [ over varname? ] [
            2dup = [ 2drop solve ]
            [ [ name>> ] dip elim ] if ] }
      { [ dup varname? ] [
            name>> swap elim ] }
      { [ 2dup [ proper-term? ] both? ] [
            2dup [ symbol>> ] bi@ =
            [ [ args>> ] bi@ <zipped> prepend solve ]
            [ recursive-term ] if
        ] }
    } cond ] unless-empty ;

GENERIC: occurs? ( varname term -- ? )
M: varname occurs? name>> = ;
M: proper-term occurs? args>> [ occurs? ] with any? ;

DEFER: pp*
! Return a substituter?
GENERIC: lift* ( subst term -- term )
: lift ( subst term -- term )
    "Lift: " write [ dup pp-subst ] [ "in term:" write dup pp ] bi*
    [ lift* ] keep over
    = [ dup " => " write pp ] unless ;

M: varname lift*
    { [ name>> of ] [ nip ] } 2|| ;
M: proper-term lift*
    [ args>> [ lift* ] with map ] [ symbol>> ] bi swap <proper-term> ;

: elim-in-term ( target-term vname term -- target-term )
    swap associate swap lift ;

:: elim ( subst problem vname term -- subst )
    vname term occurs? [ vname term recursive-term ]
    [ subst [ vname term elim-in-term ] map-values
        vname term 2array prefix
        problem [ [ vname term elim-in-term ] bi@ ] assoc-map solve ]
    if
    ;

: unify ( term1 term2 -- subst )
    2array 1array f swap solve ;

: effects>unifier ( effect1 effect2 -- consumption production subst )
    \ effect>term [
        [ effect>term ] bi@
        [ [ args>> first ] [ args>> second ] bi* ]
        [ [ args>> second ] [ args>> first ] bi* unify ] 2bi
    ] with-local-counter
    ;


! * Back-conversion
GENERIC: term>effect* ( proper-term -- seq )
PREDICATE: cons-term < proper-term symbol>> lst eq? ;
: cons>seq ( seq lst -- seq )
    dup cons-term?
    [
        dup args>> second not [ drop ]
        [
            args>> first2
            [ prefix ] dip
            cons>seq
        ] if
    ] [ prefix ] if ;

PREDICATE: stk-term < proper-term symbol>> stk eq? ;
PREDICATE: fun-term < proper-term symbol>> -- eq? ;
PREDICATE: const-term < proper-term args>> empty? ;
! M: stk-term term>effect* ( term -- effect )
!     args>> first f swap cons>seq [ term>effect* ] map ;
M: varname term>effect*
    name>> ;
: stk>effect ( term -- var-elt elts )
    stk-term check-instance
    args>> first f swap cons>seq
    dup ?first rowvarname?
    [ unclip-slice term>effect* ]
    [ f ] if swap
    [ term>effect* ] map ;
M: fun-term term>effect*
    args>> first2
    [ stk>effect ] bi@ <variable-effect>
    "quot" swap 2array ;

M: const-term term>effect*
    symbol>> "x" swap 2array ;

: funterm>effect ( funterm -- effect )
    fun-term check-instance
    term>effect* second ;

! * Prettyprinting
GENERIC: pp* ( term -- )
M: varname pp* [ name>> ] [ id>> ] bi number>string append write ;
M: proper-term pp*
    [ symbol>> name>> write ] [ "(" write args>> [ ", " write ] [ pp* ] interleave ] bi
      ")" write ;
M: word pp* name>> write ;

: pp ( term -- ) pp* nl ;


! * Whole turn
: resubst ( term subst -- term )
    [ 1array swap lift ] each ;

: unify-effects ( effect1 effect2 -- effect )
    effects>unifier
    [ resubst ] curry bi@
    [ stk>effect ] bi@ <variable-effect> ;
