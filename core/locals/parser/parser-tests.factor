USING: accessors assocs compiler.units kernel lexer locals.backend
locals.parser namespaces parser prettyprint sequences sorting
tools.test vocabs vocabs.parser ;
IN: locals.parser.tests

! XXX: remove the COMPILE< and COMPILE> below and make test-all pass

COMPILE<
! (::)
{
    "dobiedoo"
    [ 1 load-locals 1 drop-locals ]
    ( x -- y )
} [
    [
        { "dobiedoo ( x -- y ) ;" } <lexer> [ (::) ] with-lexer
    ] with-compilation-unit
    [ name>> ] 2dip
] unit-test

! parse-def
{ "um" t } [
    [
        "um" parse-def
        local>> name>>
        qualified-vocabs last words>> keys "um" swap member?
    ] with-compilation-unit
] unit-test
COMPILE>

! check-local-name
{ "hello" } [
    "hello" check-local-name
] unit-test

! make-locals
{ { "a" "b" "c" } } [
    [ { "a" "b" "c" } make-locals ] with-compilation-unit
    nip values [ name>> ] map
] unit-test

! parse-local-defs
{ { "tok1" "tok2" } } [
    [
        { "tok1 tok2 |" } <lexer> [ parse-local-defs ] with-lexer
    ] with-compilation-unit
    nip values [ name>> ] map
] unit-test

! parse-multi-def
{
    { "tok1" "tok2" }
    { "tok1" "tok2" }
} [
    [
        { "tok1 tok2 )" } <lexer> [ parse-multi-def ] with-lexer
    ] with-compilation-unit
    [ locals>> [ name>> ] map ] [ keys ] bi*
] unit-test

COMPILE<
{
    "V{ 99 set: kkk kkk }"
} [
    [
        "locals" use-vocab
        { "99 set: kkk kkk ;" } <lexer> [
            H{ } clone [ \ ; parse-until ] with-lambda-scope
        ] with-lexer
    ] with-compilation-unit unparse
] unit-test
COMPILE>
