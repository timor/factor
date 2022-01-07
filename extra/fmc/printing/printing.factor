USING: accessors arrays colors.constants fmc fmc.types formatting io
io.streams.string io.styles kernel lists make math namespaces present
prettyprint prettyprint.config prettyprint.custom prettyprint.sections sequences
types.util words ;

IN: fmc.printing

: fmc, ( obj -- )
    % ;

GENERIC: pprint-fmc* ( obj -- )
: pprint-fmc ( obj -- str )
    ! [ pprint-fmc* ] "" make ;
    [ pprint ] with-string-writer ;

: fmc. ( obj -- )
    pprint nl ;

SYMBOL: ✴
! M: +unit+ pprint* drop ✴ pprint* ;
M: +nil+ pprint-fmc* drop "✴" fmc, ;

M: varname pprint* name>> H{ { foreground COLOR: solarized-blue } } styled-text ;
M: varname pprint-fmc* name>> fmc, ;

GENERIC: pprint-loc-name ( obj -- str )
M: word pprint-loc-name name>> ;
M: +retain+ pprint-loc-name drop "ρ" ;
M: +omega+ pprint-loc-name drop "ω" ;
M: +psi+ pprint-loc-name drop "ψ" ;
M: +tau+ pprint-loc-name drop "τ" ;
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

M: fmc-cons pprint* "·" pprint-compact ;
M: fmc-cons pprint-delims drop f f ! "(" ")"
    ;
M: fmc-cons >pprint-sequence
    list>array ✴ suffix ;
! Convenience

: >fmc. ( object -- )
    nesting-limit get dup [ 100 + ] when nesting-limit
    [ >fmc fmc. ] with-variable ;

! Print types
SYMBOL: ⇒
M: fmc-type pprint* " " pprint-compact ;
M: fmc-type pprint-delims drop "(" ")" ;
M: fmc-type >pprint-sequence
    [ in>> ⇒ ]
    [ out>> ] bi 3array ;

M: type-var pprint* name>> H{ { foreground COLOR: solarized-green } } styled-text ;
M: row-type-var pprint* name>> H{ { foreground COLOR: solarized-orange } } styled-text ;
