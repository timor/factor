! Copyright (C) 2007, 2009 Slava Pestov, Eduardo Cavazos.
! See http://factorcode.org/license.txt for BSD license.
USING: lexer macros memoize parser sequences vocabs
vocabs.loader words kernel namespaces locals.parser locals.types
locals.errors ;
IN: locals

{
    "locals.macros"
    "locals.fry"
} [ require ] each

{ "locals" "prettyprint" } "locals.definitions" require-when
{ "locals" "prettyprint" } "locals.prettyprint" require-when
