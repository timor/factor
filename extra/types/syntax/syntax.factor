USING: accessors effects.parser kernel parser prettyprint.backend
prettyprint.custom quotations sequences types.typed-calls ;

IN: typed.syntax

! T( -- )[  ]
! T[  ][  ]

DEFER: )[
DEFER: ][
SYNTAX: T( ")[" parse-effect
           parse-quotation <type-call> suffix! ;

SYNTAX: T[ \ ][ parse-until >quotation
              parse-quotation <type-call> suffix! ;

M: static-type-call pprint*
    \ T( pprint-word
        [ type-spec>> pprint-effect-elements ]
        [ \ )[ pprint-word quot>> pprint-elements \ ] pprint-word ] bi ;

M: dependent-type-call pprint*
    \ T[ pprint-word
                 [ type-spec>> pprint-elements ]
                 [ \ ][ pprint-word quot>> pprint-elements \ ] pprint-word ] bi ;
