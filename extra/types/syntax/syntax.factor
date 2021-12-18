USING: accessors effects.parser io.streams.string kernel parser present
prettyprint prettyprint.backend prettyprint.custom quotations sequences
types.typed-calls ;

IN: typed.syntax

! T( -- )[  ]
! T[  ][  ]

DEFER: )[
DEFER: ][
SYNTAX: T( ")[" parse-effect
           parse-quotation <type-call> suffix! ;

SYNTAX: T[ \ ][ parse-until >quotation
              parse-quotation <type-call> suffix! ;

: pprint-body ( quot -- )
    f <inset
    pprint-elements
    block> ;

M: static-type-call pprint*
    f <inset
    \ T( pprint-word
        [ type-spec>> pprint-effect-elements ]
        [ \ )[ pprint-word quot>> pprint-body \ ] pprint-word ] bi
    block>
    ;

M: dependent-type-call pprint*
    f <inset
    \ T[ pprint-word
                 [ type-spec>> pprint-body ]
                 [ \ ][ pprint-word quot>> pprint-body \ ] pprint-word ] bi
    block>
    ;

M: type-call present
    [ pprint ] with-string-writer ;
