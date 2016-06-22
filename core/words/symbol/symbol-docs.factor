USING: help.syntax help.markup words.symbol words compiler.units ;
IN: words.symbol

HELP: symbol
{ $description "The class of symbols created by " { $link postpone\ symbol: } "." } ;

HELP: define-symbol
{ $values { "word" word } }
{ $description "Defines the word to push itself on the stack when executed. This is the run time equivalent of " { $link postpone\ symbol: } "." }
{ $notes "This word must be called from inside " { $link with-compilation-unit } "." }
{ $side-effects "word" } ;

ARTICLE: "words.symbol" "Symbols"
"A symbol pushes itself on the stack when executed. By convention, symbols are used as variable names (" { $link "namespaces" } ")."
{ $subsections
    symbol
    symbol?
}
"Defining symbols at parse time:"
{ $subsections
    postpone\ symbol:
    postpone\ SYMBOLS:
}
"Defining symbols at run time:"
{ $subsections define-symbol }
"Symbols are just compound definitions in disguise. The following two lines are equivalent:"
{ $code
    "symbol: foo"
    ": foo ( -- value ) \\ foo ;"
} ;

about: "words.symbol"
