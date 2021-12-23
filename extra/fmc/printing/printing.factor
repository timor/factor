USING: accessors arrays colors.constants fmc formatting io.streams.string
io.styles kernel make math namespaces present prettyprint prettyprint.backend
prettyprint.config prettyprint.custom prettyprint.sections sequences types.util
variants words ;

IN: fmc.printing

: fmc, ( obj -- )
    % ;

GENERIC: pprint-fmc* ( obj -- )
: pprint-fmc ( obj -- str )
    ! [ pprint-fmc* ] "" make ;
    [ pprint ] with-string-writer ;

: fmc. ( obj -- )
    pprint ;

SYMBOL: ✴
M: +unit+ pprint* drop ✴ pprint* ;
M: +unit+ pprint-fmc* drop "✴" fmc, ;

M: varname pprint* name>> H{ { foreground COLOR: solarized-blue } } styled-text ;
M: varname pprint-fmc* name>> fmc, ;

GENERIC: pprint-loc-name ( obj -- str )
M: word pprint-loc-name name>> ;
M: +retain+ pprint-loc-name drop "ρ" ;
M: f pprint-loc-name drop "λ" ;
: pprint-fmc-loc ( loc-op -- )
    loc>> pprint-loc-name fmc, ;

M: loc-pop pprint* "·" pprint-compact ;
M: loc-pop >pprint-sequence
    var>> 1array ;
M: loc-pop pprint-delims
    loc>> pprint-loc-name "%s⟨" sprintf "⟩" ;


M: loc-pop pprint-fmc*
    [ pprint-fmc-loc ]
    [ "⟨" fmc,
        var>> pprint-fmc*
        "⟩" fmc,
    ] bi ;

M: loc-push pprint* "" pprint-compact ;

M: loc-push pprint-delims
    "[" swap loc>> pprint-loc-name "]%s" sprintf ;
M: loc-push >pprint-sequence
    body>> 1array ;

M: loc-push pprint-fmc*
    [ "[" fmc,
        body>> pprint-fmc*
        "]" fmc,
    ]
    [ pprint-fmc-loc ] bi ;

M: fmc-prim pprint* obj>> pprint* ;
M: fmc-prim pprint-fmc*
    obj>> present fmc, ;

M: fmc-var pprint* "·" pprint-compact ;
M: fmc-var pprint-delims drop f f ;
M: fmc-var >pprint-sequence
    [ var>> ]
    [ cont>> ] bi 2array ;

: pprint-cont ( obj -- )
    "·" fmc, cont>> pprint-fmc* ;

M: fmc-var pprint-fmc*
    [ var>> pprint-fmc* ]
    [ pprint-cont ] bi ;

M: fmc-term pprint* "·" pprint-compact ;
M: fmc-term pprint-delims drop f f ! "(" ")"
    ;
M: fmc-term >pprint-sequence
    { { +unit+ [ +unit+ 1array ] }
      { fmc-var [ [ >pprint-sequence ] dip prefix ] }
      { fmc-abs [ [ >pprint-sequence ] dip prefix ] }
      { fmc-appl [ [ >pprint-sequence ] dip prefix ] }
     } match ;

! Convenience

: >fmc. ( object -- )
    nesting-limit get dup [ 100 + ] when nesting-limit
    [ >fmc fmc. ] with-variable ;
