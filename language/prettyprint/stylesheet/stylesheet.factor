! Copyright (C) 2009 Keith Lazuka, Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: assocs colors colors.constants combinators
combinators.short-circuit hashtables io.styles kernel literals
namespaces sequences words words.symbol ;
in: prettyprint.stylesheet

PRIVATE<

{ postpone\ USING: postpone\ use: postpone\ in: }
[
    { { foreground color: gray35 } }
    "word-style" set-word-prop
] each

PREDICATE: highlighted-word < word [ parsing-word? ] [ delimiter? ] bi or ;

PRIVATE>

symbol: base-word-style
H{ } base-word-style set-global

GENERIC: word-style ( word -- style ) ;

M: word word-style
    [ presented base-word-style get clone [ set-at ] keep ]
    [ "word-style" word-prop ] bi assoc-union! ;

symbol: highlighted-word-style
H{
    { foreground color: DarkSlateGray }
} highlighted-word-style set-global

M: highlighted-word word-style
    call-next-method highlighted-word-style get assoc-union! ;

symbol: base-string-style
H{
    { foreground color: LightSalmon4 }
} base-string-style set-global

: string-style ( str -- style )
    presented base-string-style get clone [ set-at ] keep ;

symbol: base-vocab-style
H{
    { foreground color: gray35 }
} base-vocab-style set-global

: vocab-style ( vocab -- style )
    presented base-vocab-style get clone [ set-at ] keep ;

symbol: stack-effect-style
H{
    { foreground color: FactorDarkGreen }
    { font-style plain }
} stack-effect-style set-global

: effect-style ( effect -- style )
    presented stack-effect-style get clone [ set-at ] keep ;
