USING: accessors compiler.tree kernel tools.test ;
in: compiler.tree.tests

{
    "label"
    "a-child"
} [
    "label" f "a-child" <#recursive>
    [ label>> ] [ child>> ] bi
] unit-test
