USING: accessors arrays assocs assocs.extras classes combinators
combinators.short-circuit effects hashtables io kernel math math.parser
namespaces sequences sequences.zipped sets strings types.renaming words ;

IN: types.bn-unification

FROM: namespaces => set ;

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

SYMBOL: bindings
: with-bindings ( quot -- )
    [ H{ } clone bindings ] dip with-variable ; inline

: clear-bindings ( -- )
    H{ } clone bindings set ;

: name-id ( str -- n )
    bindings get [ new-id-for ] cache ;

: fresh-name-id ( str -- n )
    bindings get [ new-id-for dup ] change-at ;

GENERIC: effect>term ( effect -- term )
M: word effect>term f <proper-term> ;
! M: string effect>term dup name-id <varname> ;
! NOTE: this is the point where we ignore named type bindings!
M: pair effect>term second effect>term ;
! M: rowvarname effect>term ;
M: varname effect>term ;
M: effect effect>term
    ! [
    [ [ in>> ] [ in-var>> ] bi prefix ]
    [ [ out>> ] [ out-var>> ] bi  prefix ] bi
    [ [ effect>term ] map>lst 1array stk swap <proper-term> ] bi@
    2array -- swap <proper-term>
    ! ] with-bindings
    ;

! Renaming
! Uniquify effect row var names
! SYMBOL: taken-names
! GENERIC: uniq-row-vars ( effect-element -- effect-element )
! M: pair uniq-row-vars
!     [ uniq-row-vars ] map ;
! M: effect uniq-row-vars
!     dup [ in-var>> ] [ out-var>> ] bi and
!     [  ] unless ;
!     [ first uniq-row-vars ] [ second ]

! ! Uniquify var names in terms
! ! Collect var names of first effect
! GENERIC: var-names ( term -- seq )
! M: varname var-names name>> 1array ;
! M: rowvarname var-names drop f ;
! M: proper-term var-names args>> [ var-names ] gather ;
! GENERIC: rowvar-names ( term -- seq )
! M: varname rowvar-names drop f ;
! M: rowvarname rowvar-names name>> 1array ;
! M: proper-term rowvar-names args>> [ var-names ] gather ;

! GENERIC: rename-vars-with ( taken-names term -- term )
! M:: var-name rename-vars-with ( taken v -- term )
!     v name>> taken member?
!     [ v name>> dup new-id-for <varname> ]
!     [ v ] if ;
! M: rowvarname rename-vars-with nip ;
! M: proper-term rename-vars-with
!     [ symbol>> ] [ args>> [ rename-vars-with ] map ] bi
!     <proper-term> ;

! GENERIC: rename-row-vars-with ( taken-names term -- term )
! M: var-name rename-row-vars-with nip ;
! M: proper-term rename-row-vars-with
!     [ symbol>> ] [ args>> [ rename-row-vars-with ] map ] bi
!     <proper-term> ;
! M:: rowvarname rename-row-vars-with ( taken rv -- term )
!     rv name>> taken member?
!     [ rv name>> dup new-id-for <rowvarname> ]
!     [ rv ] if ;

! :

! Elimination

ERROR: term-mismatch t1 t2 ;
ERROR: recursive-term vname term ;

DEFER: pp
DEFER: pp*
: pp-subst ( subst -- )
    [ [ pp* " = " write ] [ pp ] bi* ] assoc-each ;

DEFER: elim
: solve ( subst problem -- subst )
    [
        "Solve:" print
        over pp-subst
        unclip-slice first2
        2dup [ pp ] bi@
    { { [ over varname? ] [
            2dup = [ 2drop solve ]
            [ elim ] if ] }
      { [ dup varname? ] [
            swap elim ] }
      { [ 2dup [ proper-term? ] both? ] [
            2dup [ symbol>> ] bi@ =
            [ [ args>> ] bi@ <zipped> prepend solve ]
            [ term-mismatch ] if
        ] }
    } cond ] unless-empty ;

GENERIC: occurs? ( varname term -- ? )
M: varname occurs? = ;
M: proper-term occurs? args>> [ occurs? ] with any? ;

DEFER: pp*
! Return a substituter?
GENERIC: lift* ( subst term -- term )
: lift ( subst term -- term )
    "Lift: " write [ dup pp-subst ] [ "in term:" write dup pp ] bi*
    [ lift* ] keep over
    = [ dup " => " write pp ] unless ;

M: varname lift*
    { [ of ] [ nip ] } 2|| ;
M: proper-term lift*
    [ args>> [ lift* ] with map ] [ symbol>> ] bi swap <proper-term> ;

: elim-in-term ( target-term vname term -- target-term )
    swap associate swap lift ;

! Modification: If trying to eliminate a recursive term, simply drop the equation
! The equation should already be removed from the problem so simply continue.
! Alternative approach: substitute anyways
:: elim ( subst problem vname term -- subst )
    vname term occurs? [ vname term recursive-term ]
    ! vname term occurs? [
    !     "Skipping recursion: " write vname pp* " = " write term pp
    !     subst problem solve
    ! ]
    ! vname term occurs? [
    !     "Ignoring recursion: " write vname pp* " = " write term pp
    !     ! vname term 2array prefix
    !     ! problem [ [ vname term elim-in-term ] bi@ ] assoc-map solve
    ! ] when
    [ subst [ vname term elim-in-term ] map-values
        vname term 2array prefix
        problem [ [ vname term elim-in-term ] bi@ ] assoc-map solve ]
    if
    ! call
    ;

: unify ( term1 term2 -- subst )
    2array 1array f swap solve ;

: effect-terms ( effect1 effect2 -- term1 term2 )
    rename-effects
    ! [
    !     [
            [ effect>term ] bi@
            ! [ effect>term ]
            ! [ clear-bindings effect>term ] bi*
    !     ] with-bindings
    ! ] with-name-counters
    ;

: effects>unifier ( effect1 effect2 -- consumption production subst )
    effect-terms
    ! [
        [ [ args>> first ] [ args>> second ] bi* ]
        [ [ args>> second ] [ args>> first ] bi* unify ] 2bi
    ! ] with-name-counters
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
    [ name>> ] [ id>> ] bi [ number>string append ] unless-zero ;
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

! Note: works on original stuff (non-varname effect string elements)
GENERIC: simplify* ( effect -- effect )
M: string simplify* ;
M: sequence simplify* [ simplify* ] map ;
PREDICATE: nonvariable-effect < effect [ in-var>> ] [ out-var>> ] bi { [ or ] [ = ] } 2&& ;

SYMBOL: bound-row-vars
GENERIC: row-varname-used? ( name effect -- ? )

M: word row-varname-used? 2drop f ;
M: string row-varname-used? 2drop f ;
M: sequence row-varname-used?
    [ row-varname-used? ] with any? ;
M: effect row-varname-used?
    {
        [ drop bound-row-vars get in? ]
        [ in-var>> = ]
        [ out-var>> = ]
        [ in>> row-varname-used? ]
        [ out>> row-varname-used? ]
    } 2|| ;

: row-vars-used? ( effect -- ? )
    [let { [ in-var>> ] [ out-var>> ] [ in>> ] [ out>> ] } cleave
     :> ( iv ov in out )
     {
         [ iv bound-row-vars get in? ]
         [ ov bound-row-vars get in? ]
         [ iv in row-varname-used? ]
         [ iv out row-varname-used? ]
         [ ov in row-varname-used? ]
         [ ov out row-varname-used? ] } 0||
    ] ;

PREDICATE: redundant-var-effect < nonvariable-effect row-vars-used? not ;
M: redundant-var-effect simplify*
    [ in>> ] [ out>> ] bi <effect>
    simplify* ;

M: word simplify* ;
M: effect simplify*
    dup [ in-var>> ] [ out-var>> ] bi [ bound-row-vars get adjoin ] bi@
    {
        [ in-var>> ]
        [ in>> simplify* ]
        [ out-var>> ]
        [ out>> simplify* ]
    } cleave <variable-effect> ;

: simplify ( effect -- effect )
    HS{ } clone bound-row-vars [ simplify* ] with-variable ;

: unify-effects ( effect1 effect2 -- effect )
    effects>unifier
    "Result: " print dup pp-subst
    [ resubst ] curry bi@
    [ stk>effect ] bi@ <variable-effect>
    simplify
    ;
