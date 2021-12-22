USING: accessors fmc kernel make present prettyprint prettyprint.custom
sequences ;

IN: fmc.printing


: fmc, ( obj -- )
    % ;

GENERIC: pprint-fmc* ( obj -- )
: pprint-fmc ( obj -- str )
    [ pprint-fmc* ] "" make ;

: fmc. ( obj -- )
    pprint-fmc ... ;

M: fmc-seq pprint-fmc*
    "[" fmc,
    [ ";" fmc, ] [ pprint-fmc* ] interleave
    "]" fmc,
    ;

M: +unit+ pprint-fmc* drop "✴" fmc, ;
M: varname pprint-fmc* name>> fmc, ;

GENERIC: pprint-loc-name ( obj -- str )
M: word pprint-loc-name name>> ;
M: +retain+ pprint-loc-name drop "ρ" ;
M: f pprint-loc-name drop "λ" ;
: pprint-fmc-loc ( loc-op -- )
    loc>> pprint-loc-name fmc, ;

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

! M: fmc-const pprint-fmc*
!     [ prim>> pprint-fmc* ]
!     [ pprint-cont ] bi ;

M: fmc-appl pprint-fmc*
    [ push>> pprint-fmc* ]
    [ pprint-cont ] bi ;

M: fmc-abs pprint-fmc*
    [ pop>> pprint-fmc* ]
    [ pprint-cont ] bi ;

! Convenience

: >fmc. ( object -- )
    >fmc fmc. ;
