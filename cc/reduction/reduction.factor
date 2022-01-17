USING: cc classes classes.tuple kernel match sequences ;

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

SYMBOL: normalize?
: rewrite-ccn-step ( term -- term ? )
    {
        { CCN{ <?x> ?t } [ CCN{ <?x> @ ?t } sub ] } ! 1
        { CCN{ (?s@?t)?u } [ CCN{ (?s@?t)@?u } sub ] } ! 2
        { CCN{ ([?sig]<?x>.?t)?u } ! 3
          [ CCN{ (?sig :: <?x> -> ?u)?t } sub ] if }
        { T{ app f T{ ref f ?x } ?u } ! 3.1
          [| | ?x deref :> rr T{ app f rr ?u } sub ] }
        { CCN{ I ?u } [ ?u t ] } ! 4
        { CCN{ (?sig :: <?x> -> ?t)<?x> } [ ?t t ] } ! 5
        { CCN{ (?sig :: <?x> -> ?t)<?z> } ! 6
          [ CCN{ ?sig <?z> } sub ] }
        ! TODO: dangerous? If we see a ref, we know it's closed, so we can just drop the env?
        { T{ app f T{ ext f ?sig ?t } T{ ref f ?u } }
          [ T{ ref f ?u } sub ]
        }
        { CCN{ (?sig :: <?x> -> ?t)(?u@?v) } ! 7
          [ CCN{ ((?sig :: <?x> -> ?t)?u)((?sig :: <?x> -> ?t)?v) } sub ] }
        { CCN{ (?sig :: <?x> -> ?t)([?rho]<?z>.?s) } ! 8
          [ CCN{ [(?sig :: <?x> -> ?t)?rho]<?z>.?s } sub ] }
        { CCN{ (?sig :: <?x> -> ?t)I } ! 9
          [ I t ] }
        { CCN{ (?sig :: <?x> -> ?t)(?rho :: <?z> -> ?u) } ! 10
          [ CCN{ (?sig :: <?x> -> ?t)?rho :: <?z> -> (?sig :: <?x> -> ?t)?u } sub ]
        }
        ! Deref mappings in immediate position
        ! NOTE: Too eager, not needed?
        ! { T{ ext f ?sig T{ mapping f ?x T{ ref f ?t } } }
        !   [| | ?t deref :> tt T{ ext f ?sig T{ mapping f ?x tt } } sub ]
        ! }
        [
            {
                { [ normalize? get [ dup ref? ] [ f ] if ] [ word>> deref t ] }
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

: rewrite-ccn ( term -- term )
    rewrite-ccn-cached ;

CONSTANT: omega CCN{ [I]z.[I,z]f.[I,z,f]x.f@(z@z@f)@x }
CONSTANT: Y CCN{ [I :: z -> omega]f.[I,z,f]x.f@(z@z@f)@x }

! Functional Pearl, Scott encodings

CONSTANT: Nil CCN{ [I]f.[I,f]g.f }
CONSTANT: Cons CCN{ [I]x.[I,x]xs.[I,x,xs]f.[I,x,xs,f]g.(g x xs) }
CONSTANT: Head CCN{ [I]xs.(xs undef [I]x.[I,x]xs.x) }
CONSTANT: Tail CCN{ [I]xs.(xs undef [I]x.[I,x]xs.xs) }

CONSTANT: True CCN{ [I]a.[I,a]b.a }
CONSTANT: False CCN{ [I]a.[I,a]b.b }
CONSTANT: Ifte CCN{ [I]t.t }

CONSTANT: Zero CCN{ [I]f.[I,f]g.f }
CONSTANT: Suc CCN{ [I]n.[I,n]f.[I,n,f]g.(g n) }
CONSTANT: Pred CCN{ [I]n.(n undef [I]m.m) }
CONSTANT: One CCN{ Suc Zero }
CCN: Zerop [I]x.( x True [I]n.False ) ;

CCN: Add [I]n.[I,n]m.( n m [I,m]n.(Suc (Add n m) ) ) ;
CONSTANT: Add_ CCN{ [I]add.[I,add]n.[I,add,n]m.(n m [I,add,m]n.(Suc (add add n m))) }
CONSTANT: Add2 CCN{ Add_ Add_ }
CCN: Add_y Y ([I]add.[I,add]n.[I,add,n]m.(n m [I,add,m]n.(Suc add n m))) ;

CCN: Length [I]x.(x Zero ([I]x.[I,x]xs.(Suc (Length xs)))) ;
