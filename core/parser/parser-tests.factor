USING: accessors arrays assocs classes compiler.units effects
eval generic grouping io.pathnames io.streams.string kernel
lexer math multiline namespaces parser sequences sets
source-files source-files.errors strings tools.crossref
tools.test vocabs vocabs.parser words words.symbol ;
in: parser.tests

{ 1 [ 2 [ 3 ] 4 ] 5 }
[ "1\n[\n2\n[\n3\n]\n4\n]\n5" eval( -- a b c ) ]
unit-test

{ t t f f }
[ "t t f f" eval( -- ? ? ? ? ) ]
unit-test

{ "hello world" }
[ "\"hello world\"" eval( -- string ) ]
unit-test

{ "\n\r\t\\" }
[ "\"\\n\\r\\t\\\\\"" eval( -- string ) ]
unit-test

{ "hello world" }
[
"#!/usr/bin/env factor
\"hello world\"" eval( -- string )
] unit-test

{ "hello world" }
[
    "in: parser.tests : hello ( -- str ) \"hello world\" ;"
    eval( -- ) "use: parser.tests hello" eval( -- string )
] unit-test

[ "in: parser.tests : \" ( -- n ) 123 ;" eval( -- ) ]
[ error>> invalid-word-name? ] must-fail-with
[ "in: parser.tests : \"asdf ( -- n ) 123 ;" eval( -- ) ]
[ error>> invalid-word-name? ] must-fail-with
[ "in: parser.tests : 123 ( -- n ) 123 ;" eval( -- ) ]
[ error>> invalid-word-name? ] must-fail-with

{ }
[ "! This is a comment, people." eval( -- ) ]
unit-test

! Test escapes

{ " " }
[ "\"\\u000020\"" eval( -- string ) ]
unit-test

{ "'" }
[ "\"\\u000027\"" eval( -- string ) ]
unit-test

! Test EOL comments in multiline strings.
{ "Hello" } [ "! This calls until-eol.\n\"Hello\"" eval( -- string ) ] unit-test

{ word } [ \ f class-of ] unit-test

! Test stack effect parsing

: effect-parsing-test ( a b -- c ) + ;

{ t } [
    "effect-parsing-test" "parser.tests" lookup-word
    \ effect-parsing-test eq?
] unit-test

{ T{ effect f { "a" "b" } { "c" } f } }
[ \ effect-parsing-test "declared-effect" word-prop ] unit-test

: baz ( a b -- * ) 2array throw ;

{ t }
[ \ baz "declared-effect" word-prop terminated?>> ]
unit-test

{ } [ "in: parser.tests use: math : effect-parsing-test ( a b -- d ) - ;" eval( -- ) ] unit-test

{ t } [
    "effect-parsing-test" "parser.tests" lookup-word
    \ effect-parsing-test eq?
] unit-test

{ T{ effect f { "a" "b" } { "d" } f } }
[ \ effect-parsing-test "declared-effect" word-prop ] unit-test

[ "in: parser.tests : missing-- ( a b ) ;" eval( -- ) ] must-fail

! Funny bug
{ 2 } [ "in: parser.tests : \0. ( -- x ) 2 ; \0." eval( -- n ) ] unit-test

defer: foo

"in: parser.tests USING: math prettyprint ; SYNTAX: foo 2 2 + . ;" eval( -- )

{ } [ "use: parser.tests foo" eval( -- ) ] unit-test

"in: parser.tests USING: math prettyprint ; : foo ( -- ) 2 2 + . ;" eval( -- )

{ t } [
    "use: parser.tests \\ foo" eval( -- word )
    "foo" "parser.tests" lookup-word eq?
] unit-test

! parse-tokens should do the right thing on EOF
[ "USING: kernel" eval( -- ) ]
[ error>> T{ unexpected { want "token" } } = ] must-fail-with

! Test smudging

{ 1 } [
    "in: parser.tests : smudge-me ( -- ) ;" <string-reader> "foo"
    parse-stream drop

    "foo" path>source-file definitions>> first cardinality
] unit-test

{ t } [ "smudge-me" "parser.tests" lookup-word >boolean ] unit-test

{ } [
    "in: parser.tests : smudge-me-more ( -- ) ;" <string-reader> "foo"
    parse-stream drop
] unit-test

{ t } [ "smudge-me-more" "parser.tests" lookup-word >boolean ] unit-test
{ f } [ "smudge-me" "parser.tests" lookup-word >boolean ] unit-test

{ 3 } [
    "in: parser.tests USING: math strings ; GENERIC: smudge-me ( a -- b ) ; M: integer smudge-me ; M: string smudge-me ;" <string-reader> "foo"
    parse-stream drop

    "foo" path>source-file definitions>> first cardinality
] unit-test

{ 1 } [
    "in: parser.tests USING: arrays ; M: array smudge-me ;" <string-reader> "bar"
    parse-stream drop

    "bar" path>source-file definitions>> first cardinality
] unit-test

{ 2 } [
    "in: parser.tests USING: math strings ; GENERIC: smudge-me ( a -- b ) ; M: integer smudge-me ;" <string-reader> "foo"
    parse-stream drop

    "foo" path>source-file definitions>> first cardinality
] unit-test

{ t } [
    array "smudge-me" "parser.tests" lookup-word order member-eq?
] unit-test

{ t } [
    integer "smudge-me" "parser.tests" lookup-word order member-eq?
] unit-test

{ f } [
    string "smudge-me" "parser.tests" lookup-word order member-eq?
] unit-test

{ } [
    "in: parser.tests use: math 2 2 +" <string-reader> "a"
    parse-stream drop
] unit-test

{ t } [
    "a" <pathname> \ + usage member?
] unit-test

{ } [
    "in: parser.tests use: math 2 2 -" <string-reader> "a"
    parse-stream drop
] unit-test

{ f } [
    "a" <pathname> \ + usage member?
] unit-test

{ } [
    "a" source-files get delete-at
    2 [
        "in: parser.tests defer: x : y ( -- ) x ; : x ( -- ) y ;"
        <string-reader> "a" parse-stream drop
    ] times
] unit-test

"a" source-files get delete-at

[
    "in: parser.tests : x ( -- ) ; : y ( -- * ) 3 throw ; this is an error"
    <string-reader> "a" parse-stream
] [ source-file-error? ] must-fail-with

{ t } [
    "y" "parser.tests" lookup-word >boolean
] unit-test

{ f } [
    "in: parser.tests : x ( -- ) ;"
    <string-reader> "a" parse-stream drop
    "y" "parser.tests" lookup-word
] unit-test

! Test new forward definition logic
{ } [
    "in: axx : axx ( -- ) ;"
    <string-reader> "axx" parse-stream drop
] unit-test

{ } [
    "use: axx in: bxx : bxx ( -- ) ; : cxx ( -- ) axx bxx ;"
    <string-reader> "bxx" parse-stream drop
] unit-test

! So we move the bxx word to axx...
{ } [
    "in: axx : axx ( -- ) ; : bxx ( -- ) ;"
    <string-reader> "axx" parse-stream drop
] unit-test

{ t } [ "bxx" "axx" lookup-word >boolean ] unit-test

! And reload the file that uses it...
{ } [
    "use: axx in: bxx ( -- ) : cxx ( -- ) axx bxx ;"
    <string-reader> "bxx" parse-stream drop
] unit-test

! And hope not to get a forward-error!

! Turning a generic into a non-generic could cause all
! kinds of funnyness
{ } [
    "in: ayy use: kernel GENERIC: ayy ( a -- b ) ; M: object ayy ;"
    <string-reader> "ayy" parse-stream drop
] unit-test

{ } [
    "in: ayy use: kernel : ayy ( -- ) ;"
    <string-reader> "ayy" parse-stream drop
] unit-test

{ } [
    "in: azz TUPLE: my-class ; GENERIC: a-generic ( a -- b ) ;"
    <string-reader> "azz" parse-stream drop
] unit-test

{ } [
    "use: azz M: my-class a-generic ;"
    <string-reader> "azz-2" parse-stream drop
] unit-test

{ } [
    "in: azz GENERIC: a-generic ( a -- b ) ;"
    <string-reader> "azz" parse-stream drop
] unit-test

{ } [
    "use: azz use: math M: integer a-generic ;"
    <string-reader> "azz-2" parse-stream drop
] unit-test

{ } [
    "in: parser.tests : <bogus-error> ( -- ) ; : bogus ( -- error ) <bogus-error> ;"
    <string-reader> "bogus-error" parse-stream drop
] unit-test

{ } [
    "in: parser.tests TUPLE: bogus-error ; C: <bogus-error> bogus-error : bogus ( -- error ) <bogus-error> ;"
    <string-reader> "bogus-error" parse-stream drop
] unit-test

! Problems with class predicates -vs- ordinary words
{ } [
    "in: parser.tests TUPLE: killer ;"
    <string-reader> "removing-the-predicate" parse-stream drop
] unit-test

{ } [
    "in: parser.tests GENERIC: killer? ( a -- b ) ;"
    <string-reader> "removing-the-predicate" parse-stream drop
] unit-test

{ t } [
    "killer?" "parser.tests" lookup-word >boolean
] unit-test

[
    "in: parser.tests TUPLE: another-pred-test ; GENERIC: another-pred-test? ( a -- b ) ;"
    <string-reader> "removing-the-predicate" parse-stream
] [ error>> error>> error>> redefine-error? ] must-fail-with

[
    "in: parser.tests TUPLE: class-redef-test ; TUPLE: class-redef-test ;"
    <string-reader> "redefining-a-class-1" parse-stream
] [ error>> error>> error>> redefine-error? ] must-fail-with

{ } [
    "in: parser.tests TUPLE: class-redef-test ; symbol: class-redef-test"
    <string-reader> "redefining-a-class-2" parse-stream drop
] unit-test

[
    "in: parser.tests TUPLE: class-redef-test ; symbol: class-redef-test : class-redef-test ( -- ) ;"
    <string-reader> "redefining-a-class-3" parse-stream drop
] [ error>> error>> error>> redefine-error? ] must-fail-with

{ } [
    "in: parser.tests TUPLE: class-fwd-test ;"
    <string-reader> "redefining-a-class-3" parse-stream drop
] unit-test

[
    "in: parser.tests \\ class-fwd-test"
    <string-reader> "redefining-a-class-3" parse-stream drop
] [ error>> error>> error>> no-word-error? ] must-fail-with

{ } [
    "in: parser.tests TUPLE: class-fwd-test ; symbol: class-fwd-test"
    <string-reader> "redefining-a-class-3" parse-stream drop
] unit-test

[
    "in: parser.tests \\ class-fwd-test"
    <string-reader> "redefining-a-class-3" parse-stream drop
] [ error>> error>> error>> no-word-error? ] must-fail-with

[
    "in: parser.tests : foo ( -- ) ; TUPLE: foo ;"
    <string-reader> "redefining-a-class-4" parse-stream drop
] [ error>> error>> error>> redefine-error? ] must-fail-with

{ } [
    "in: parser.tests : foo ( x y -- z ) 1 2 ; : bar ( a -- b ) ;" eval( -- )
] unit-test

[
    "in: parser.tests : foo ( x y -- z) 1 2 ; : bar ( a -- b ) ;" eval( -- )
] must-fail

{ } [
    "in: parser.tests use: kernel PREDICATE: foo < object ;" eval( -- )
] unit-test

{ t } [
    "foo" "parser.tests" lookup-word last-word eq?
] unit-test

{ } [
    [
        "redefining-a-class-5" forget-source
        "redefining-a-class-6" forget-source
        "redefining-a-class-7" forget-source
    ] with-compilation-unit
] unit-test

2 [
    [ ] [
        "in: parser.tests TUPLE: foo ; GENERIC: foo ( a -- b ) ;"
        <string-reader> "redefining-a-class-5" parse-stream drop
    ] unit-test

    [ ] [
        "in: parser.tests M: f foo ;"
        <string-reader> "redefining-a-class-6" parse-stream drop
    ] unit-test

    [ f ] [ f "foo" "parser.tests" lookup-word execute ] unit-test

    [ ] [
        "in: parser.tests TUPLE: foo ; GENERIC: foo ( a -- b ) ;"
        <string-reader> "redefining-a-class-5" parse-stream drop
    ] unit-test

    [ f ] [ f "foo" "parser.tests" lookup-word execute ] unit-test

    [ ] [
        "in: parser.tests TUPLE: foo ; GENERIC: foo ( a -- b ) ;"
    <string-reader> "redefining-a-class-7" parse-stream drop
    ] unit-test

    [ f ] [ f "foo" "parser.tests" lookup-word execute ] unit-test

    [ ] [
        "in: parser.tests TUPLE: foo ;"
        <string-reader> "redefining-a-class-7" parse-stream drop
    ] unit-test

    [ t ] [ "foo" "parser.tests" lookup-word symbol? ] unit-test
] times

[ "vocab:parser/test/assert-depth.factor" run-file ] must-fail

2 [
    [ ] [
        "in: parser.tests defer: d-f-s d-f-s symbol: d-f-s d-f-s"
        <string-reader> "d-f-s-test" parse-stream drop
    ] unit-test

    [ ] [
        "in: parser.tests defer: d-f-s d-f-s forget: d-f-s symbol: d-f-s d-f-s"
        <string-reader> "d-f-s-test" parse-stream drop
    ] unit-test

    [ ] [
        "in: parser.tests defer: d-f-s d-f-s symbol: d-f-s d-f-s"
        <string-reader> "d-f-s-test" parse-stream drop
    ] unit-test
] times

{ } [
    [ "this-better-not-exist" forget-vocab ] with-compilation-unit
] unit-test

[
    "use: this-better-not-exist" eval( -- )
] must-fail

[ ": foo ;" eval( -- ) ] [ error>> error>> no-current-vocab-error? ] must-fail-with

{ 92 } [ "char: \\" eval( -- n ) ] unit-test
{ 92 } [ "char: \\\\" eval( -- n ) ] unit-test

{ } [
    {
        "in: parser.tests"
        "USING: math arrays kernel ;"
        "GENERIC: change-combination ( obj a -- b ) ;"
        "M: integer change-combination 2drop 1 ;"
        "M: array change-combination 2drop 2 ;"
    } "\n" join <string-reader> "change-combination-test" parse-stream drop
] unit-test

{ } [
    {
        "in: parser.tests"
        "USING: math arrays kernel ;"
        "GENERIC# change-combination 1 ( obj a -- b )"
        "M: integer change-combination 2drop 1 ;"
        "M: array change-combination 2drop 2 ;"
    } "\n" join <string-reader> "change-combination-test" parse-stream drop
] unit-test

{ 2 } [
    "change-combination" "parser.tests" lookup-word
    "methods" word-prop assoc-size
] unit-test

{ } [
    2 [
        "in: parser.tests defer: twice-fails forget: twice-fails mixin: twice-fails"
        <string-reader> "twice-fails-test" parse-stream drop
    ] times
] unit-test

{ [ ] } [
    "in: parser.tests : staging-problem-test-1 ( -- a ) 1 ; : staging-problem-test-2 ( -- a ) staging-problem-test-1 ;"
    <string-reader> "staging-problem-test" parse-stream
] unit-test

{ t } [ "staging-problem-test-1" "parser.tests" lookup-word >boolean ] unit-test

{ t } [ "staging-problem-test-2" "parser.tests" lookup-word >boolean ] unit-test

{ [ ] } [
    "in: parser.tests << : staging-problem-test-1 ( -- a ) 1 ; >> : staging-problem-test-2 ( -- a ) staging-problem-test-1 ;"
    <string-reader> "staging-problem-test" parse-stream
] unit-test

{ t } [ "staging-problem-test-1" "parser.tests" lookup-word >boolean ] unit-test

{ t } [ "staging-problem-test-2" "parser.tests" lookup-word >boolean ] unit-test

[ "defer: blahy" eval( -- ) ] [ error>> error>> no-current-vocab-error? ] must-fail-with

[
    "in: parser.tests SYNTAX: blahy ; forget: blahy" eval( -- )
] [
    error>> staging-violation?
] must-fail-with

! Bogus error message
defer: blahy

[ "in: parser.tests use: kernel TUPLE: blahy < tuple ; : blahy ( -- ) ; TUPLE: blahy < tuple ; : blahy ( -- ) ;" eval( -- ) ]
[ error>> error>> def>> \ blahy eq? ] must-fail-with

[ "char: \\u9999999999999" eval( -- n ) ] must-fail

SYMBOLS: a b c ;

{ a } [ a ] unit-test
{ b } [ b ] unit-test
{ c } [ c ] unit-test

defer: blah

{ } [ "in: parser.tests GENERIC: blah ( x -- x )" eval( -- ) ; ] unit-test
{ } [ "in: parser.tests SYMBOLS: blah ;" eval( -- ) ] unit-test

{ f } [ \ blah generic? ] unit-test
{ t } [ \ blah symbol? ] unit-test

defer: blah1

[ "in: parser.tests SINGLETONS: blah1 blah1 blah1 ;" eval( -- ) ]
[ error>> error>> def>> \ blah1 eq? ]
must-fail-with

in: qualified.tests.foo
: x ( -- a ) 1 ;
: y ( -- a ) 5 ;
in: qualified.tests.bar
: x ( -- a ) 2 ;
: y ( -- a ) 4 ;
in: qualified.tests.baz
: x ( -- a ) 3 ;

QUALIFIED: qualified.tests.foo
QUALIFIED: qualified.tests.bar
{ 1 2 3 } [ qualified.tests.foo:x qualified.tests.bar:x x ] unit-test

QUALIFIED-WITH: qualified.tests.bar p
{ 2 } [ p:x ] unit-test

RENAME: x qualified.tests.baz => y
{ 3 } [ y ] unit-test

FROM: qualified.tests.baz => x ;
{ 3 } [ x ] unit-test
{ 3 } [ y ] unit-test

EXCLUDE: qualified.tests.bar => x ;
{ 3 } [ x ] unit-test
{ 4 } [ y ] unit-test

! Two similar bugs

! Replace : def with something in << >>
/* { [ ] } [
    "in: parser.tests : was-once-a-word-bug ( -- ) ;"
    <string-reader> "was-once-a-word-test" parse-stream
] unit-test

{ t } [ "was-once-a-word-bug" "parser.tests" lookup-word >boolean ] unit-test

{ [ ] } [
    "in: parser.tests use: words << \"was-once-a-word-bug\" \"parser.tests\" create-word [ ] ( -- ) define-declared >>"
    <string-reader> "was-once-a-word-test" parse-stream
] unit-test

{ t } [ "was-once-a-word-bug" "parser.tests" lookup-word >boolean ] unit-test */

! Replace : def with defer:
{ [ ] } [
    "in: parser.tests : is-not-deferred ( -- ) ;"
    <string-reader> "is-not-deferred" parse-stream
] unit-test

{ t } [ "is-not-deferred" "parser.tests" lookup-word >boolean ] unit-test
{ f } [ "is-not-deferred" "parser.tests" lookup-word deferred? ] unit-test

{ [ ] } [
    "in: parser.tests defer: is-not-deferred"
    <string-reader> "is-not-deferred" parse-stream
] unit-test

{ t } [ "is-not-deferred" "parser.tests" lookup-word >boolean ] unit-test
{ t } [ "is-not-deferred" "parser.tests" lookup-word deferred? ] unit-test

! Forward-reference resolution case iterated using list in the wrong direction
{ [ ] } [
    "in: parser.tests.forward-ref-1 defer: x defer: y"
    <string-reader> "forward-ref-1" parse-stream
] unit-test

{ [ ] } [
    "in: parser.tests.forward-ref-2 defer: x defer: y"
    <string-reader> "forward-ref-2" parse-stream
] unit-test

{ [ ] } [
    "in: parser.tests.forward-ref-3 FROM: parser.tests.forward-ref-1 => x y ; FROM: parser.tests.forward-ref-2 => x y ; : z ( -- ) x y ;"
    <string-reader> "forward-ref-3" parse-stream
] unit-test

{ t } [
    "z" "parser.tests.forward-ref-3" lookup-word def>> [ vocabulary>> ] map all-equal?
] unit-test

{ [ ] } [
    "FROM: parser.tests.forward-ref-1 => x y ; FROM: parser.tests.forward-ref-2 => x y ; in: parser.tests.forward-ref-3 : x ( -- ) ; : z ( -- ) x y ;"
    <string-reader> "forward-ref-3" parse-stream
] unit-test

{ f } [
    "z" "parser.tests.forward-ref-3" lookup-word def>> [ vocabulary>> ] map all-equal?
] unit-test

{ [ ] } [
    "in: parser.tests.forward-ref-3 FROM: parser.tests.forward-ref-1 => x y ; FROM: parser.tests.forward-ref-2 => x y ; : z ( -- ) x y ;"
    <string-reader> "forward-ref-3" parse-stream
] unit-test

{ t } [
    "z" "parser.tests.forward-ref-3" lookup-word def>> [ vocabulary>> ] map all-equal?
] unit-test

{ [ dup ] } [
    "use: kernel dup" <string-reader> "unuse-test" parse-stream
] unit-test

[
    "dup" <string-reader> "unuse-test" parse-stream
] [ error>> error>> error>> no-word-error? ] must-fail-with

[
    "use: kernel UNuse: kernel dup" <string-reader> "unuse-test" parse-stream
] [ error>> error>> error>> no-word-error? ] must-fail-with

{ } [ [ "vocabs.loader.test.l" forget-vocab ] with-compilation-unit ] unit-test

[
    [ "vocabs.loader.test.l" use-vocab ] must-fail
    [ f ] [ "vocabs.loader.test.l" manifest get search-vocab-names>> in? ] unit-test
    [ ] [ "vocabs.loader.test.l" unuse-vocab ] unit-test
    [ f ] [ "vocabs.loader.test.l" manifest get search-vocab-names>> in? ] unit-test
] with-file-vocabs

! Test cases for #183
[ "singleton: 33" <string-reader> "class identifier test" parse-stream ]
[ error>> lexer-error? ] must-fail-with

[ ": 44 ( -- ) ;" <string-reader> "word identifier test" parse-stream ]
[ error>> lexer-error? ] must-fail-with

[ "GENERIC: 33 ( -- ) ;" <string-reader> "generic identifier test" parse-stream ]
[ error>> lexer-error? ] must-fail-with

{ t } [
    t auto-use? [
        { private? } use-first-word?
    ] with-variable
] unit-test
