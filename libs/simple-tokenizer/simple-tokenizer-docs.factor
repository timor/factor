USING: help.markup help.syntax strings ;
in: simple-tokenizer

HELP: tokenize
{ $values { "input" string } { "ast" "a sequence of strings" } }
{ $description
    "Tokenize a string. Supported syntax:"
    { $list
        { { $snippet "foo bar baz" } " - simple tokens" }
        { { $snippet "foo\\ bar" } " - token with an escaped space" }
        { { $snippet "\"foo bar\"" } " - quoted token" }
    }
} ;
