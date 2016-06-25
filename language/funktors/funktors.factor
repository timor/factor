USING: accessors effects.parser eval grouping interpolate kernel
multiline namespaces parser sequences sets splitting
vocabs.parser words ;
IN: funktors

SYNTAX: \ funktor[[ "]]" parse-multiline-string
    manifest get search-vocab-names>>
    { "syntax" } diff members
    current-vocab name>> ".private" ?tail drop ".private" append suffix
    $[
        _ interpolate>string
        current-vocab name>> "\nIN: " "\n" surround prepend
        _ 5 group [ " " join ] map "\n" join
        "USING: " " ;\n" surround prepend
        eval( -- )
    ] suffix! ;

SYNTAX: \ FUNKTOR:
    scan-new-escaped scan-effect scan-object
    $[ _ call ] swap define-declared ;
