USING: accessors fmc kernel make present prettyprint prettyprint.custom
sequences ;

IN: fmc.printing


: fmc, ( obj -- )
    % ;

GENERIC: pprint-fmc* ( obj -- )
: pprint-fmc ( obj -- str )
    [ pprint-fmc* ] "" make ;

: fmc. ( obj -- )
    pprint-fmc . ;

M: fmc-seq pprint-fmc*
    dup pprint-delims swap name>> fmc,
    [ [ ";" fmc, ] [ pprint-fmc* ] interleave ] dip
    name>> fmc, ;

M: +unit+ pprint-fmc* drop "⋆" fmc, ;
M: varname pprint-fmc* name>> fmc, ;

: pprint-fmc-loc ( loc-op -- )
    loc>> [ name>> ] [ "λ" ] if* fmc, ;

M: loc-pop pprint-fmc*
    [ pprint-fmc-loc ]
    [ "⟨" fmc,
        var>> pprint-fmc*
        "⟩" fmc,
    ] bi ;
M: loc-push pprint-fmc*
    [ "[" fmc,
        body>> pprint-fmc*
        "]" fmc,
    ]
    [ pprint-fmc-loc ] bi ;

M: fmc-prim pprint-fmc*
    obj>> present fmc, ;

: pprint-cont ( obj -- )
    "·" fmc, cont>> pprint-fmc* ;

M: fmc-var pprint-fmc*
    [ var>> pprint-fmc* ]
    [ pprint-cont ] bi ;

M: fmc-const pprint-fmc*
    [ prim>> pprint-fmc* ]
    [ pprint-cont ] bi ;

M: fmc-appl pprint-fmc*
    [ push>> pprint-fmc* ]
    [ pprint-cont ] bi ;

M: fmc-abs pprint-fmc*
    [ pop>> pprint-fmc* ]
    [ pprint-cont ] bi ;
