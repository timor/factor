USING: accessors arrays assocs assocs.extras classes combinators
combinators.short-circuit effects hashtables io kernel math math.order sequences
sequences.zipped terms types.base-types types.function-types types.renaming ;

IN: types.bn-unification

FROM: namespaces => set ;

! TUPLE: proper-term
!     { symbol }
!     { args sequence } ;
! C: <proper-term> proper-term

! SYMBOLS: lst nil ;
! : cons ( car cdr -- cons )
!     2array lst swap <proper-term> ;

! ! Reverse-mapping
! ! nil = ( f . f )
! ERROR: need-dotted-list ;
! :: map>lst ( seq quot: ( x -- y ) -- lst )
!     seq empty? [ need-dotted-list
!                  ! lst f <proper-term>
!     ]
!     [
!         seq length 1 = [ seq first quot call( x -- y ) ]
!         [

!             seq unclip-last-slice :> ( rest head )
!             head quot call( x -- y ) :> car
!             car rest quot map>lst cons
!         ] if
!     ] if ;

! SYMBOLS: -- stk const ;

! GENERIC: effect>term ( effect -- term )
! M: word effect>term f <proper-term> ;
! ! M: string effect>term dup name-id <varname> ;
! ! NOTE: this is the point where we ignore named type bindings!
! M: pair effect>term second effect>term ;
! ! M: rowvarname effect>term ;
! M: varname effect>term ;
! M: effect effect>term
!     [ [ in>> ] [ in-var>> ] bi prefix ]
!     [ [ out>> ] [ out-var>> ] bi  prefix ] bi
!     [ [ effect>term ] map>lst 1array stk swap <proper-term> ] bi@
!     2array -- swap <proper-term>
!     ;

! Elimination

ERROR: proper-term-mismatch t1 t2 ;
ERROR: recursive-term vname term ;

DEFER: pp
DEFER: pp*
: pp-subst ( subst -- )
    [ [ pp* " = " write ] [ pp ] bi* ] assoc-each ;

DEFER: elim
! NOTE This is important: For some reason, being eager with substituting the
! recursive types leads to intermediate recursive terms.  Actually, I'm not
! really sure they are intermediate...
! For now the solution seems to be to postpone solving the recursion equation
! until the end
DEFER: solve

! NOTE: Approach right now is to carry the dup onto the right side
: solve-dup-type-var ( subst problem dup-var term -- subst  )
    ! [ -1 swap change-term-var-order dup ] dip <rec-type> elim ;
    [ -1 swap change-term-var-order dup ] dip <rec-type> 2array suffix solve ;

: lift ( subst term -- term )
    "Lift: " write [ dup pp-subst ] [ "in term:" write dup pp* ] bi*
    [ lift* ] keep over
    = [ dup " => " write pp ] [ nl ] if ;

! Re-instantiation rule: M = rec(x|E(x)) => M' = E(M)
:: solve-rec-type ( subst problem term1 term2 -- subst )
    term2 [ rec-var>> ] [ element>> ] bi :> ( rv expr )
    term1 :> inst-var
    inst-var rv associate expr lift :> instantiated
    ! NOTE: again 2 possibilities: 1. solve immediately, 2. solve last
    subst problem inst-var propagate-duplication instantiated 2array
    ! prefix solve
    suffix solve
    ;

: not-a-dup-type-var ( subst problem term1 term2 -- subst )
    dup rec-type? [ swap ] unless
    dup rec-type? not
    [ proper-term-mismatch ]
    [ solve-rec-type ] if ;

: term-mismatch ( subst problem term1 term2 -- subst )
    over dup-type-var? [ swap ] unless
    over dup-type-var? not
    ! [ not-a-dup-type-var ]
    [ proper-term-mismatch ]
    [ solve-dup-type-var ] if ;

DEFER: solve1
! : solve-dup-type ( subst problem dup-term rhs -- subst )
!     [ element>> ] [ propagate-duplication ] bi*
!     ! propagate-duplication
!     solve1 ;

: solve-dup-type ( subst problem dup-term rhs -- subst )
    [ element>> dup ] dip <rec-type> 2array suffix solve ;
! [ propagate-duplication ] bi*
!     ! propagate-duplication
!     solve1 ;


: solve-drop-type ( subst problem drop-term rhs -- subst )
    nip [ propagate-duplication ] keep solve1 ;

: solve1 ( subst problem lhs rhs -- subst )
    "Solve1:" print
    2dup [ "! " write pp* " = " write ] [ pp ] bi*
    {
        { [ dup drop-type? ]
          [ swap solve1 ] }
        { [ over drop-type? ]
          [ solve-drop-type ] }
        { [ over base-type-var? ] [
              2dup = [ 2drop solve ]
              [ elim ] if ] }
        { [ dup base-type-var? ] [
              swap elim ] }
        ! { [ over term-var? ] [
        !       2dup = [ 2drop solve ]
        !       [ elim ] if ] }
        ! { [ dup term-var? ] [
        !       swap elim ] }
        { [ dup dup-type? ]
          [ swap solve-dup-type ] }
        { [ over dup-type? ]
          [ solve-dup-type ] }
        { [ 2dup [ proper-term? ] both? ] [
              2dup [ class-of ] bi@ =
              [ [ args>> ] bi@ <zipped> prepend solve ]
              [ proper-term-mismatch ] if
          ] }
        [ term-mismatch ]
    } cond ;

: solve ( subst problem -- subst )
    [
        over pp-subst
        unclip-slice first2
        solve1
    ] unless-empty ;

! GENERIC: occurs? ( varname term -- ? )
! M: term-varvarname occurs? = ;
! M: proper-term occurs? args>> [ occurs? ] with any? ;

! DEFER: pp*
! ! Return a substituter?
! GENERIC: lift* ( subst term -- term )
! M: varname lift*
!     { [ of ] [ nip ] } 2|| ;
! M: proper-term lift*
!     [ args>> [ lift* ] with map ] [ symbol>> ] bi swap <proper-term> ;

: elim-in-term ( target-term vname term -- target-term )
    swap associate swap lift ;

! Modification: If trying to eliminate a recursive term, simply drop the equation
! The equation should already be removed from the problem so simply continue.
! Alternative approach: substitute anyways
:: elim ( subst problem vname term -- subst )
    vname term occurs-free? [ vname term recursive-term ]
    ! vname term occurs? [
    !     "Skipping recursion: " write vname pp* " = " write term pp
    !     subst problem solve
    ! ]
    ! vname term occurs? [
    !     "Ignoring recursion: " write vname pp* " = " write term pp
    !     ! vname term 2array prefix
    !     ! problem [ [ vname term elim-in-term ] bi@ ] assoc-map solve
    ! ] when
    [
        subst [ [ vname term elim-in-term ] bi@ ] assoc-map
        ! subst [ vname term elim-in-term ] map-values
        vname term 2array prefix
        problem [ [ vname term elim-in-term ] bi@ ] assoc-map solve ]
    if
    ! call
    ;

: unify ( term1 term2 -- subst )
    2array 1array f swap solve ;

! : effect-terms ( effect1 effect2 -- term1 term2 )
!     [ effect>term ]
!     rename-effects
!     ! [
!     !     [
!             [ effect>term ] bi@
!             ! [ effect>term ]
!             ! [ clear-bindings effect>term ] bi*
!     !     ] with-bindings
!     ! ] with-name-counters
!     ;

: effects>unifier ( fun-type1 fun-type2 -- consumption production subst )
    ! [ effect>term ] bi@
    rename-2-terms
    "Computing unifier:" print
    2dup [ pp ] bi@
    ! [
        [ [ consumption>> ] [ production>> ] bi* ]
        [ [ production>> ] [ consumption>> ] bi* unify ] 2bi
    ! ] with-name-counters
    ;


! ! * Back-conversion
! GENERIC: term>effect* ( proper-term -- seq )
! PREDICATE: cons-term < proper-term symbol>> lst eq? ;
! : cons>seq ( seq lst -- seq )
!     dup cons-term?
!     [
!         dup args>> second not [ drop ]
!         [
!             args>> first2
!             [ prefix ] dip
!             cons>seq
!         ] if
!     ] [ prefix ] if ;

! PREDICATE: stk-term < proper-term symbol>> stk eq? ;
! PREDICATE: fun-term < proper-term symbol>> -- eq? ;
! PREDICATE: const-term < proper-term args>> empty? ;
! ! M: stk-term term>effect* ( term -- effect )
! !     args>> first f swap cons>seq [ term>effect* ] map ;
! M: varname term>effect*
!     [ name>> ] [ id>> ] bi [ number>string append ] unless-zero ;
! : stk>effect ( term -- var-elt elts )
!     stk-term check-instance
!     args>> first f swap cons>seq
!     dup ?first rowvarname?
!     [ unclip-slice term>effect* ]
!     [ f ] if swap
!     [ term>effect* ] map ;
! M: fun-term term>effect*
!     args>> first2
!     [ stk>effect ] bi@ <variable-effect>
!     "quot" swap 2array ;

! M: const-term term>effect*
!     symbol>> "x" swap 2array ;

! : funterm>effect ( funterm -- effect )
!     fun-term check-instance
!     term>effect* second ;

! * Prettyprinting
GENERIC: pp* ( term -- )
! M: varname pp* [ name>> ] [ id>> ] bi number>string append write ;
M: type-var pp* effect>string write ;
! M: type-var pp*
!     [ name>> ]
!     [ id>> number>string append ]
!     [ order>> CHAR: ' <string> append ] tri write ;
M: proper-term pp* effect>string write ;
! M: fun-type pp* effect>string write ;
! M: proper-term pp*
!     [ symbol>> name>> write ] [ "(" write args>> [ ", " write ] [ pp* ] interleave ] bi
!       ")" write ;
! M: word pp* name>> write ;

: pp ( term -- ) pp* nl ;


! * Whole turn
: resubst ( term subst -- term )
    [ 1array swap lift ] each ;

! Note: works on original stuff (non-varname effect string elements)
! GENERIC: simplify* ( effect -- effect )
! M: string simplify* ;
! M: sequence simplify* [ simplify* ] map ;
! PREDICATE: nonvariable-effect < effect [ in-var>> ] [ out-var>> ] bi { [ or ] [ = ] } 2&& ;

! SYMBOL: bound-row-vars
! GENERIC: row-varname-used? ( name effect -- ? )

! M: word row-varname-used? 2drop f ;
! M: string row-varname-used? 2drop f ;
! M: sequence row-varname-used?
!     [ row-varname-used? ] with any? ;
! M: effect row-varname-used?
!     {
!         [ drop bound-row-vars get in? ]
!         [ in-var>> = ]
!         [ out-var>> = ]
!         [ in>> row-varname-used? ]
!         [ out>> row-varname-used? ]
!     } 2|| ;

! : row-vars-used? ( effect -- ? )
!     [let { [ in-var>> ] [ out-var>> ] [ in>> ] [ out>> ] } cleave
!      :> ( iv ov in out )
!      {
!          [ iv bound-row-vars get in? ]
!          [ ov bound-row-vars get in? ]
!          [ iv in row-varname-used? ]
!          [ iv out row-varname-used? ]
!          [ ov in row-varname-used? ]
!          [ ov out row-varname-used? ] } 0||
!     ] ;

! PREDICATE: redundant-var-effect < nonvariable-effect row-vars-used? not ;
! M: redundant-var-effect simplify*
!     [ in>> ] [ out>> ] bi <effect>
!     simplify* ;

! M: word simplify* ;
! M: effect simplify*
!     dup [ in-var>> ] [ out-var>> ] bi [ bound-row-vars get adjoin ] bi@
!     {
!         [ in-var>> ]
!         [ in>> simplify* ]
!         [ out-var>> ]
!         [ out>> simplify* ]
!     } cleave <variable-effect> ;

! : simplify ( effect -- effect )
!     HS{ } clone bound-row-vars [ simplify* ] with-variable ;

! Noticed that not all substitutions are oriented correctly in the final unifier
! necessarily.  Hopefully that's not a bug?  Re-orienting the substitutions in
! case there is ambiguity, so that it is used in the problem.
! If the rhs is a term-var, and the lhs does not appear in the target terms,
! then swap the substitution pair
: re-orient-subst-pair ( terms varname replacement -- varname replacement )
    dup term-var?
    [| terms lhs rhs |
     lhs terms [ occurs-free? ] with any?
     [ lhs rhs ]
     [ rhs lhs ] if
    ] [ nipd ] if ;

: re-orient-subst ( consumption production subst -- consumption production subst )
    [ 2dup 2array ] dip [ swapd re-orient-subst-pair ] with assoc-map ;

GENERIC: convert-var-orders* ( assoc level term -- assoc term )
M: type-var convert-var-orders*
    [ type-var-key pick push-at ]
    [ [ name>> ] [ id>> ] bi rot type-var boa ] 2bi
    ;
M: dup-type convert-var-orders*
    [ 1 + ] [ element>> ] bi* convert-var-orders* ;
M: proper-term convert-var-orders*
    [ convert-var-orders* ] with map-args ;

: convert-var-orders ( term -- assoc term )
    [ H{ } clone 0 ] dip convert-var-orders*
    [ [ infimum ] map-values ] dip ;

GENERIC: adjust-var-orders* ( assoc term -- term )
M: type-var adjust-var-orders*
    [ type-var-key swap at 0 or neg ] keep change-term-var-order ;
M: proper-term adjust-var-orders*
    [ adjust-var-orders* ] with map-args ;

: normalize-var-orders ( term -- term )
    convert-var-orders adjust-var-orders* ;

GENERIC: normalize-recs ( term -- term )
: reducible-rec-type? ( rec-type -- ? )
    [ rec-var>> ] [ element>> ] bi
    ! occurs-free? not ;
    { [ = ] [ occurs-free? not ] } 2|| ;

M: rec-type normalize-recs
    dup reducible-rec-type?
    [ element>> normalize-recs ]
    [ [ normalize-recs ] map-args ] if ;
    ! [ [ rec-var>> ] [ element>> ] bi normalize-recs <rec-type> ]
    ! ;
    ! dup [ rec-var>> ] [ element>> ] bi normalize-recs
    ! [ occurs-free? ] keep swap
    ! [ drop ] [ nip ] if ;
M: type-var normalize-recs ;
M: proper-term normalize-recs
    [ normalize-recs ] map-args ;

! : normalize-fun-type ( fun-type -- fun-type )

: unify-effects ( effect1 effect2 -- effect )
    effects>unifier ! For dup expansion
    ! re-orient-subst
    "Result: " print dup pp-subst
    [ resubst ] curry bi@ <fun-type>
    normalize-recs
    normalize-var-orders
    effect>term
    ! [ stk>effect ] bi@ <variable-effect>
    ! simplify
    ;
