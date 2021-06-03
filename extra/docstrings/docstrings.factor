USING: assocs help help.markup kernel make namespaces regexp regexp.combinators
sequences strings strings.parser unicode vocabs.parser ;

IN: docstrings


! NOTE: >string is only here because matches? does not allow string slices
: find-and-apply ( str rules -- )
    [ >string ] dip dupd [ first matches? ] with find swap [ second call( str -- ) ] [ 2drop ] if ;

: regexp-transform ( str rules -- )
    [ keys <or> all-matching-slices ]
    [ [ find-and-apply ] curry each ] bi ;

SYMBOL: current-text
: tok ( -- ) current-text get >string [ , ] unless-empty
    SBUF"" clone current-text set ;

: ,text ( str -- ) current-text get swap append! drop ;

CONSTANT: docstring-transforms {
    { R/ \b[A-Z0-9_-]+\b/ [ tok >lower <$snippet> , ] }
    { R/ `.+`/ [ tok rest-slice but-last vocabs.parser:search <$link> , ] }
    { R/ '.+'/ [ tok rest-slice but-last <$snippet> , ] }
    { R/ \n\n/ [ tok \ $nl , ] }
    { R/ ./ [ ,text ] }
}

! It doesn't get much more inefficient than that in parsing, I guess...
: parse-docstring ( str -- seq )
    docstring-transforms [ tok regexp-transform tok ] { } make ;

SYMBOL: last-docstring

: help-from-docstring ( word -- help )
    word-help*
    last-docstring get-global \ $description prefix suffix ;

: set-help-from-docstring ( word -- )
    [ help-from-docstring ] [ set-word-help ] bi ;

SYNTAX: DOC" parse-string parse-docstring last-docstring set-global ;
