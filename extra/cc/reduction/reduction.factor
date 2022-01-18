USING: accessors assocs cc cc.defined classes classes.tuple combinators kernel
match namespaces sequences ;

IN: cc.reduction

! * CCN reduction
MATCH-VARS: ?x ?s ?t ?u ?v ?z ?sig ?rho ;

: sub ( term -- term ? )
    replace-patterns t ; inline

DEFER: rewrite-ccn-step
GENERIC: decompose-ccn ( term -- term ? )
M: I decompose-ccn f ;
M: ccn-term decompose-ccn
    [ tuple-slots f swap [ rewrite-ccn-step swap [ or ] dip ] map swap ]
    [ swap [ class-of slots>tuple ] dip ] bi ;
M: var decompose-ccn f ;

: deref ( word -- term )
    ccn-def ;

: rewrite-ccn-step ( term -- term ? )
    {
        { CCN{ <?x> ?t } [ CCN{ <?x> @ ?t } sub ] } ! 1
        { CCN{ (?s@?t)?u } [ CCN{ (?s@?t)@?u } sub ] } ! 2
        ! (λ[σ]x.t)u => (σ::x→u)t
        { CCN{ ([?sig]<?x>.?t)?u } ! 3
          [ CCN{ (?sig :: <?x> -> ?u)?t } sub ] if }
        { CCN{ I ?u } [ ?u t ] } ! 4
        { CCN{ (?sig :: <?x> -> ?t)<?x> } [ ?t t ] } ! 5
        { CCN{ (?sig :: <?x> -> ?t)<?z> } ! 6
          [ CCN{ ?sig <?z> } sub ] }
        { CCN{ (?sig :: <?x> -> ?t)(?u@?v) } ! 7
          [ CCN{ ((?sig :: <?x> -> ?t)?u)((?sig :: <?x> -> ?t)?v) } sub ] }
        { CCN{ (?sig :: <?x> -> ?t)([?rho]<?z>.?s) } ! 8
          [ CCN{ [(?sig :: <?x> -> ?t)?rho]<?z>.?s } sub ] }
        { CCN{ (?sig :: <?x> -> ?t)I } ! 9
          [ I t ] }
        { CCN{ (?sig :: <?x> -> ?t)(?rho :: <?z> -> ?u) } ! 10
          [ CCN{ (?sig :: <?x> -> ?t)?rho :: <?z> -> (?sig :: <?x> -> ?t)?u } sub ]
        }
        [
            {
                { [ dup ref? ] [ word>> deref t ] }
                { [ dup ccn-term? ] [ decompose-ccn ] }
                [ f ]
            } cond
        ]
    } match-cond ;


MEMO: rewrite-ccn-step-cached ( term -- term ? )
    rewrite-ccn-step ;

: rewrite-ccn-uncached ( term -- term )
    [ rewrite-ccn-step-cached ] loop ;

MEMO: rewrite-ccn-cached ( term -- term )
    rewrite-ccn-uncached ;

SYMBOL: normal-cache
normal-cache [ H{ } clone ] initialize

: find-cached-ref ( term -- term ? )
    normal-cache get ?at
    [ <ref> t ] [ f ] if ;
GENERIC: find-ccn-ref ( term -- term )
M: object find-ccn-ref ;
M: var find-ccn-ref ;
M: I find-ccn-ref ;
M: app find-ccn-ref
    find-cached-ref
    [
        [ left>> find-ccn-ref ]
        [ right>> find-ccn-ref ] bi
        <app>
    ] unless ;

M: tapp find-ccn-ref
    find-cached-ref
    [
        [ left>> find-ccn-ref ]
        [ right>> find-ccn-ref ] bi
        <tapp>
    ] unless ;

M: abs find-ccn-ref
    find-cached-ref
    [
        [ subst>> find-ccn-ref ]
        [ var>> ]
        [ term>> find-ccn-ref ] tri
        <abs>
    ] unless ;

M: mapping find-ccn-ref
    [ var>> ]
    [ term>> find-ccn-ref ] bi <mapping> ;
M: ext find-ccn-ref
    [ prev>> find-ccn-ref ]
    [ mapping>> find-ccn-ref ] bi <ext> ;

: reduce-ccn ( term -- term )
    rewrite-ccn-cached ;

: rewrite-ccn ( term -- term )
    reduce-ccn find-ccn-ref ;
