USING: accessors arrays assocs assocs.extras combinators.short-circuit
hashtables kernel match patterns.reduction patterns.terms sequences sets typed
types.util ;

IN: patterns.dynamic

FROM: syntax => _ ;
FROM: patterns.terms => undefined ;

UNION: matchable-symbol host-constructor match-sym ;

PREDICATE: data-compound < app-term head-term matchable-symbol? ;
UNION: data-structure matchable-symbol data-compound host-data __ ;
UNION: matchable data-structure case ;

! Dynamic pattern calculus term syntax
UNION: term match-var matchable app-term case case-def ;

! * Substitution Formals

GENERIC: fv ( term -- set )
M: match-var fv 1array ;
M: assoc fv [ fv ] map-values ;
M: app-term fv
    left/right
    [ fv ] bi@ union ;

! Static case
! : syms ( subst -- set )
!     [ keys ] [ fv ] bi union ;

! Specific to dynamic patterns:

M: match-sym fv drop f ;
M: case fv
    [ pattern>> fv ]
    [ body>> fv ]
    [ binding-syms>> ] tri diff union ;

GENERIC: fm ( term -- set )
M: match-var fm drop f ;
M: match-sym fm word>> 1array ;
M: app-term fm left/right [ fm ] bi@ union ;
M: case fm
    [ pattern>> fm ]
    [ binding-syms>> diff ]
    [ body>> fm ] tri union ;

: closed? ( term -- ? )
    fv null? ;

: syms ( subst -- symbols )
    [ keys ]
    [ fv ]
    [ fm ] tri union union ;

GENERIC: avoids? ( subst syms -- ? )
M: match-var avoids?
    swap syms in? not ;
M: sequence avoids?
    [ avoids? ] with all? ;

GENERIC: vsubst ( subst term -- term )
M: match-var vsubst ?of drop ;
! :: maybe-rebuild-app-term ( left right orig -- app-term )
!     { [ orig left>> left eq? ] [ orig right>> right eq? ] } 0&&
!     [ orig ]
!     [ left right orig new-app-term ] if ;

M:: app-term vsubst ( subst term -- term )
    term [ left/right ]
    [ [ subst swap vsubst ] bi@ ]
    [ term new-app-term ] ?rebuild ;

M: match-sym vsubst nip ;

! TYPED:: maybe-rebuild-case-term ( bindings pattern body orig: case -- case-term )
!     { [ orig pattern>> pattern eq? ] [ orig body>> body eq? ] } 0&&
!     [ orig ]
!     [ bindings pattern body <case> ] if ;

M:: case vsubst ( subst term -- term )
    subst term binding-syms>> avoids?
    [ term [ [ pattern>> ] [ body>> ] bi ]
      [ [ subst swap vsubst ] bi@ ]
      [ term binding-syms>> -rot <case> ]
      ?rebuild ]
    [ term ] if ;

! NOTE: specific case for msubst really needed?
GENERIC: msubst ( subst term -- term )
M: match-var msubst nip ;
M: match-sym msubst
    ! ?of drop ;
    2dup word>> swap key?
    [ word>> vsubst ]
    [ nip ] if ;

M:: app-term msubst ( subst term -- term )
    term [ left/right ]
    [ [ subst swap msubst ] bi@ ]
    [ term new-app-term ] ?rebuild ;

M:: case msubst ( subst term -- term )
    subst term binding-syms>> avoids?
    [ term [ [ pattern>> ] [ body>> ] bi ]
      [ [ subst swap msubst ] bi@ ]
      [ term binding-syms>> -rot <case> ]
      ?rebuild ]
    [ term ] if ;

GENERIC: basic-matching ( term seq pattern -- result: match-result )
M:: match-sym basic-matching ( term seq pattern -- result: match-result )
    pattern word>> :> var
    var seq in?
    [ term var associate ]
    [ term seq pattern call-next-method ] if ;

M: matchable basic-matching
    pick over = [ 3drop f ]
    [ call-next-method ] if ;

M: __ basic-matching 3drop f ;

M:: app-term basic-matching ( term seq pattern -- result: match-result )
    pattern left/right :> ( l r )
    { [ term app-term? ]
      [ l r [ matchable? ] both? ] } 0&&
    [
        term left/right :> ( tl tr )
        tl seq l basic-matching
        tr seq r basic-matching
        match-disjoint-union
    ] [ term seq pattern call-next-method ] if ;

! This results in an endless loop when using recursive definitions without using
! Solution: (?)
! Only reduce patterns recursively.  This should be safe if we have only
! left-linear patterns...

M: case pc-reduce-step ( term -- term ? )
    dup pattern>> reduce-all
    [ [ [ binding-syms>> ] [ body>> ] bi ] dip swap <case> t ]
    [ drop f ] if ;

M: object basic-matching ( term seq pattern -- result: match-result )
    nip [ matchable? ] both? none undefined ? ;

GENERIC: check-match ( seq res: match-result -- res': match-result )
M: match-result check-match nip ;
M: assoc check-match 2dup keys set= [ nip ] [ 2drop none ] if ;

TYPED: dynamic-matching ( term: term seq pattern: term -- res: match-result )
    [ basic-matching ] keepd swap check-match ;

M: case do-match-rule ( c: case u: term -- result: match-app )
    swap [ binding-syms>> ] [ pattern>> ] [ body>> ] tri
    [ dynamic-matching ] dip match-rule ;
