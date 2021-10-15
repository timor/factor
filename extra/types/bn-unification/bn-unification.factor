USING: accessors arrays assocs assocs.extras classes combinators
combinators.short-circuit effects hashtables io kernel math math.order
namespaces prettyprint sequences sequences.zipped terms tools.continuations
types.algebra types.base-types types.function-types types.renaming types.util
types.value-types ;

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
ERROR: recursive-term-error vname term ;

DEFER: pp
GENERIC: pp* ( term -- )
: pp-subst ( subst -- )
    [ [ pp* " = " write ] [ pp ] bi* ] assoc-each ;
M: assoc pp*
    pp-subst ;

DEFER: elim
! NOTE This is important: For some reason, being eager with substituting the
! recursive types leads to intermediate recursive terms.  Actually, I'm not
! really sure they are intermediate...
! For now the solution seems to be to postpone solving the recursion equation
! until the end
DEFER: solve

! ! NOTE: Approach right now is to carry the dup onto the right side
! : solve-dup-type-var ( subst problem dup-var term -- subst  )
!     ! [ -1 swap change-term-var-order dup ] dip <rec-type> elim ;
!     [ -1 swap change-term-var-order dup ] dip <rec-type> 2array suffix solve ;

:: lift ( subst term -- term )
    subst term lift* :> result
    term result =
    t or
    [
        "Lift: " write subst pp-subst "in term:" write
        term pp* " => " write result pp
    ] unless
    result
    ;
    ! [ lift* ] keep over
    ! = [ dup " => " write pp ] [ nl ] if ;

! Re-instantiation rule: M = rec(x|E(x)) => M' = E(M)
! :: solve-rec-type ( subst problem term1 term2 -- subst )
!     term2 [ rec-var>> ] [ element>> ] bi :> ( rv expr )
!     term1 :> inst-var
!     inst-var rv associate expr lift :> instantiated
!     ! NOTE: again 2 possibilities: 1. solve immediately, 2. solve last
!     subst problem inst-var propagate-duplication instantiated 2array
!     ! prefix solve
!     suffix solve
!     ;

! : not-a-dup-type-var ( subst problem term1 term2 -- subst )
!     dup rec-type? [ swap ] unless
!     dup rec-type? not
!     [ proper-term-mismatch ]
!     [ solve-rec-type ] if ;

! : term-mismatch ( subst problem term1 term2 -- subst )
!     over dup-type-var? [ swap ] unless
!     over dup-type-var? not
!     ! [ not-a-dup-type-var ]
!     [ proper-term-mismatch ]
!     [ solve-dup-type-var ] if ;

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

! Drop types.  Equation is drop(foo) = M.
! Effect is to take all variables in M, and immediately count down all
! occurrences of the corresponding variables above n for all x(n) ∊ M
! Unfortunately, orders may be messed up, if any lhs changes in the substitutions, this could be
! problematic.
: map-rhs ( eqs quot: ( term -- term ) -- eqs )
    map-values ; inline

: map-problem ( eqs quot: ( term -- term ) -- eqs )
    '[ _ bi@ ] assoc-map ; inline

! : solve-drop-type ( subst problem drop-term rhs -- subst )
!     nip term-vars [
!         [ swap lower-var-order ] curry
!         [ map-problem ] [ map-problem ] bi-curry bi*
!     ] each
!     solve
!     ;
    ! free-vars
    ! nip [ propagate-duplication ] keep solve1 ;

: skip-eqn ( subst problem lhs rhs -- subst )
    "Discarding equation: " write 2dup [ pp* " = " write ] [ pp ] bi*
    proper-term-mismatch
    2drop solve ;

! NOTE: Should be the same as solving Pa=x and Sa = x in parallel! ( but doesnt seem to )
: solve-drop-type ( subst problem drop-term rhs -- subst )
    nip <unique-var> <drop>
    ! nip <unique-var>
    solve1
    ;
: solve-drop-type-doesnt-work ( subst problem drop-term rhs -- subst )
    nip
    <unique-var>
    [ [ <pred> ] dip 2array ]
    [ [ <succ> ] dip 2array ] 2bi 2array
    ! break
    prepend solve ;


! : maybe-solve-drop ( subst problem lhs rhs -- subst )
!     {
!         { [ dup drop-type? ]
!           [ swap solve-drop-type ] }
!         { [ over drop-type? ]
!           [ solve-drop-type ] }
!         [ skip-eqn ]
!     } cond ;

UNION: PSD PS drop-type ;

! Normalized, possible forms here:
! 1. Pa = Pb
! 2. Sa = Sb
! 3. Sa = Pb
! 4. foo = Pb
! 5. foo = Sb
! 6. Dx = Pb
! 7. Dx = Sb
! 7. Sb = foo
! 8. Sb = Dx

: ?1eqn ( lhs rhs ? quot -- eqns/f )
    '[ @ 2array 1array ]
    [ 2drop f ] if ; inline

: decompose-same ( lhs rhs -- eqns/f )
    2dup { [ [ succ-type? ] both? ] [ [ pred-type? ] both? ] } 2||
    [ [ element>> ] bi@ ] ?1eqn ;

! PREDICATE: drop-var < drop-type element>> term-var? ;

: should-swap-PS? ( lhs rhs -- ? )
    [ drop-type? ] [ { [ PS? ] [ element>> term-var? ] } 1&& ] bi* or ;

: decompose-swap-P ( lhs rhs -- eqns/f )
    dup pred-type? [ swap ] unless
    dup pred-type?
    2over should-swap-PS? and [
        [ propagate-succ ] [ element>> ] bi* [ simplify-psd ] bi@
    ] ?1eqn ;

: decompose-swap-S ( lhs rhs -- eqns/f )
    dup succ-type? [ swap ] unless
    dup succ-type?
    2over should-swap-PS? and [
        [ propagate-pred ] [ element>> ] bi* [ simplify-psd ] bi@
    ] ?1eqn ;

! : decompose-swap-PS ( lhs rhs -- eqns/f )
!     2dup [ { [ PS? ] [ element>> term-var? ] } 1&& ] either?
!     [ { [ decompose-swap-P ] [ decompose-swap-S ] } 2|| ]
!     [ 2drop f ] if
!     ;

: decompose-D ( lhs rhs -- eqns/f )
    2dup { [ [ drop-type? ] either? ] [ [ PSD? ] both? ] } 2&&
    [ [ element>> ] bi@ ] ?1eqn ;
    ! dup drop-type? [ swap ] unless
    ! dup drop-type?
    ! 2over [ PS? ] either? and
    ! ! NOTE: could be wrong here because of stuff
    ! [ decompose-swap-PS ]
    ! [ 2drop f ] if ;

: decompose-PS-args ( lhs PS-term -- lhs rhs )
    dup pred-type?
    [ element>> [ propagate-pred ] map-args ]
    [ element>> [ propagate-succ ] map-args ] if ;

: decompose-PS-term ( lhs rhs -- eqns/f )
    dup PS? [ swap ] unless
    dup element>> args>>
    [ decompose-PS-args ] ?1eqn ;

: decompose-PS-problems ( lhs rhs -- eqns )
    {
        [ decompose-same ]
        ! [ decompose-D ]
        ! [ decompose-swap-PS ]
        [ decompose-swap-P ]
        [ decompose-swap-S ]
        [ decompose-PS-term ]
        [ proper-term-mismatch ]
    } 2|| ;

: solve-decompose-PS ( subst problem lhs rhs -- subst )
    dup pred-type?
    [ swap ] unless
    decompose-PS-problems
    break
    prepend solve ;

: solve-rec-type ( subst problem rec-type rhs -- subst )
    swap instantiate-rec-type solve1 ;


! Instantiation: One side is a template, the other is a duplicate-sum-type
! thingy.  The template needs to be duplicated and instantiated with fresh
! variables, and a substituter added to the problem that replaces the original
! variables in the template with the duplicates.
: solve-instance ( subst problem lhs rhs -- subst )
    dup sum-type? [ swap ] unless
    instantiate-alternatives prepend solve ;

: solve-choice ( subst problem lhs rhs -- subst )
    dup choice-type? [ swap ] unless
    [ then>> ] [ else>> ] bi 2array [ 2array ] with map prepend solve ;

! NOTE: promoting here!
: solve-conditional ( subst problem lhs rhs -- subst )
    over maybe-type? [ swap ] unless
    <unique-var> swap <maybe-type> swap solve1 ;

GENERIC: proper-term-type ( proper-term -- type )

M: proper-term proper-term-type
    class-of ;
M: type-const proper-term-type
    thing>> ;

M: type-const term-value-type thing>> ;
! M: lazy-computation term-value-type
!     word>> stack-effect effect-out-types
!     dup length 1 = not
!     [ "trying to take result of non-applicative lazy computation" throw ] when
!     first ;

UNION: data-type type-const eval-result ;

: solve1 ( subst problem lhs rhs -- subst )
    [
        "Solve1:" print
        2dup [ "! " write pp* " = " write ] [ pp ] bi*
    ] 3 when-debug
    {
        { [ 2dup [ +any+? ] either? ]
          [ 2drop solve ]
        }
        { [ over term-var? ] [
              2dup = [ 2drop solve ]
              [ elim ] if ] }
        { [ dup term-var? ] [
              swap elim ] }
        { [ 2dup [ sum-type? ] both? ]
          [ "both-sided alternative decomposition " 3array throw ] }
        { [ 2dup { [ [ choice-type? ] either? ] [ [ choice-type? ] both? not ] } 2&& ]
          [ solve-choice ]
        }
        { [ 2dup { [ [ sum-type? ] either? ] [ [ sum-type? ] both? not ] } 2&& ]
          [ solve-instance ]
        }
        ! NOTE: allowing here because of expansion
        ! { [ 2dup [ maybe-type? ] both? ]
        !   [ "both-sided conditional term" 3array throw ] }
        { [ 2dup { [ [ maybe-type? ] either? ] [ [ maybe-type? ] both? not ] } 2&& ]
          [ solve-conditional ] }
        ! TODO: This should probably take into account variance position here.
        ! I guess allowing only intersection of base types is the most one can
        ! get out of syntax-directed typing...
        { [ 2dup [ data-type? ] both? ]
          [ 2dup [ term-value-type ] bi@ value-types-intersect?
            [ 2drop solve ]
            [ skip-eqn ] if ]
        }
        { [ 2dup [ proper-term? ] both? ] [
              2dup [ proper-term-type ] bi@ =
              [ [ args>> ] bi@ <zipped> prepend solve ]
              [
                  skip-eqn
              ] if
          ] }
        [
            skip-eqn
            ! proper-term-mismatch
        ]
    } cond ;

: pp-problem ( subst problem -- )
    nl "Problem:" print pp*
    "Substitutions:" print pp ;

: solve ( subst problem -- subst )
    [
        [ 2dup pp-problem ] 2 when-debug
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

: elim-rec ( subst problem vname term -- subst )
    dupd abstract-rec-type elim ;

: subst-in-term ( target-term vname term -- target-term )
    swap associate swap lift ;

! Modification: If trying to eliminate a recursive term, simply drop the equation
! The equation should already be removed from the problem so simply continue.
! Alternative approach: substitute anyways
:: elim ( subst problem vname term -- subst )
    ! vname term occurs-free? [ subst problem vname term elim-rec ]
    ! vname term occurs-free? drop f [ subst problem vname term elim-rec ]
    vname term occurs-free? [ vname term recursive-term-error ]

    ! vname term occurs? [
    !     "Skipping recursion: " write vname pp* " = " write term pp
    !     subst problem solve
    ! ]
    ! vname term occurs? [
    !     "Ignoring recursion: " write vname pp* " = " write term pp
    !     ! vname term 2array prefix
    !     ! problem [ [ vname term subst-in-term ] bi@ ] assoc-map solve
    ! ] when
    [
        ! subst [ [ vname term subst-in-term ] bi@ ] assoc-map
        subst [ vname term subst-in-term ] map-values
        vname term 2array prefix
        problem [ [ vname term subst-in-term ] bi@ ] assoc-map solve ]
    if
    ! call
    ;

: unify ( term1 term2 -- subst )
    2array 1array f swap solve ;

: unify-with-constraints ( eqns term1 term2 -- subst )
    2array prefix f swap solve ;

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

: effects>unifier ( effect-type1 effect-type2 -- consumption production subst )
    [ effect>term ] bi@
    rename-2-terms
    ! [ [ get-constraints ] bi@ append ] 2keep
    [ f ] 2dip
    [
        "Computing unifier:" print
        2dup [ . ] bi@
        "Constraints:" print pick pp
    ] 1 when-debug
    ! [
        [ [ production>> ] [ consumption>> ] bi* unify-with-constraints ]
        [ [ consumption>> ] [ production>> ] bi* ] 2bi rot
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
M: term pp* effect>string write ;
! M: varname pp* [ name>> ] [ id>> ] bi number>string append write ;
! M: type-var pp* effect>string write ;
! M: type-var pp*
!     [ name>> ]
!     [ id>> number>string append ]
!     [ order>> CHAR: ' <string> append ] tri write ;
! M: proper-term pp* effect>string write ;
! M: fun-type pp* effect>string write ;
! M: proper-term pp*
!     [ symbol>> name>> write ] [ "(" write args>> [ ", " write ] [ pp* ] interleave ] bi
!       ")" write ;
! M: word pp* name>> write ;

! M: drop-type pp* effect>string write ;

: pp ( term -- ) pp* nl ;


! * Whole turn
: resubst ( term subst -- term )
    [ 1array swap lift ] each ;

GENERIC: collect-min-var-orders* ( assoc term -- assoc )
M: type-var collect-min-var-orders*
    [ order>> ] [ type-var-key ] bi pick [ [ min ] when* ] change-at ;
M: proper-term collect-min-var-orders*
    [ collect-min-var-orders* ] each-arg ;

: collect-min-var-orders ( term -- assoc )
    H{ } clone swap collect-min-var-orders* ;

: normalize-var-orders ( term -- term )
    dup collect-min-var-orders
    [ neg swap rot change-term-var-orders ] assoc-each ;

GENERIC: simplify-rec ( term -- term )
M: term simplify-rec ;
M: proper-term simplify-rec
    [ simplify-rec ] map-args ;
: unused-binding? ( rec-type -- ? )
    [ rec-var>> ] [ element>> ] bi occurs-free? not ;
: trivial-body? ( rec-type -- ? )
    [ rec-var>> ] [ element>> ] bi = ;
M: rec-type simplify-rec
    dup { [ unused-binding? ] [ trivial-body? ] } 1||
    [ element>> ] when ;


! This should return something that can be used on the typed effect level
: normalize-effect-type ( fun-type -- effect-type )
    simplify-var-names
    [ "Result type: " write dup pp ] 2 when-debug
    ! eliminate-drop-terms
    ! "Eliminated drops: " write dup pp
    ! simplify-rec
    ! "Simplified Recursion: " write dup pp
    ! convert-to-vars
    ! eliminate-pred/succ ; replaced by convert-to-vars
    ! normalize-var-orders
    ! TODO: somehow not cleaning up doesnt work.  Bug in renaming???
    ! cleanup-fun-type
    [ simplify-term* cleanup-unused swap [ or ] dip swap ] loop
    ! simplify-term
    [ "Simplified: " write dup pp ] 2 when-debug
    ;

: unify-effects ( effect1 effect2 -- effect )
    effects>unifier ! For dup expansion
    ! re-orient-subst
    [ "Unifier: " print dup pp-subst ] 2 when-debug
    [ <fun-type> ] dip
    [ "Target: " write over pp ] 2 when-debug
    ! [ resubst ] curry bi@ <fun-type>
    resubst
    [ "Substituted: " write dup pp ] 2 when-debug
    normalize-effect-type
    [ "Normalized: " write dup pp nl ] 1 when-debug
    ;
