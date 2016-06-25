USING: help.markup help.syntax literals sequences strings ;
IN: vocabs.files

HELP: vocab-tests-path
{ $values { "vocab" "a vocabulary specifier" } { "path" "pathname string to test file" } }
{ $description "Outputs a pathname where the unit test file for " { $snippet "vocab" } " is located.  Outputs " { $link f } " if the vocabulary does not have a directory on disk." } ;

HELP: vocab-tests-file
{ $values { "vocab" "a vocabulary specifier" } { "path/f" "pathname string to test file" } }
{ $description "Outputs a pathname where the unit test file is located, or " { $link f } " if the file does not exist." } ;

HELP: vocab-tests-dir
{ $values { "vocab" "a vocabulary specifier" } { "paths" "a sequence of pathname strings" } }
{ $description "Outputs a sequence of pathnames for the tests in the test directory." } ;

HELP: vocab-files
{ $values { "vocab" "a vocabulary specifier" } { "seq" "a sequence of pathname strings" } }
{ $description "Outputs a sequence of files comprising this vocabulary, or " { $link f } " if the vocabulary does not have a directory on disk." }
{ $examples
  { $example
    "USING: prettyprint vocabs.files ; "
    "\"alien.libraries\" vocab-files ."
    $$[
        {
            "{"
            "    \"vocab:alien/libraries/libraries.factor\""
            "    \"vocab:alien/libraries/libraries-docs.factor\""
            "    \"vocab:alien/libraries/libraries-tests.factor\""
            "}"
        } "\n" join
    ]
  }
} ;

HELP: vocab-tests
{ $values { "vocab" "a vocabulary specifier" } { "tests" "a sequence of pathname strings" } }
{ $description "Outputs a sequence of pathnames where the unit tests for " { $snippet "vocab" } " are located." }
{ $examples
  { $example
    "USING: prettyprint sorting vocabs.files ; "
    "\"xml\" vocab-tests natural-sort ."
    $$[
        {
            "{"
            "    \"vocab:xml/tests/cdata.factor\""
            "    \"vocab:xml/tests/encodings.factor\""
            "    \"vocab:xml/tests/funny-dtd.factor\""
            "    \"vocab:xml/tests/soap.factor\""
            "    \"vocab:xml/tests/state-parser-tests.factor\""
            "    \"vocab:xml/tests/templating.factor\""
            "    \"vocab:xml/tests/test.factor\""
            "    \"vocab:xml/tests/xmltest.factor\""
            "    \"vocab:xml/tests/xmode-dtd.factor\""
            "}"
        } "\n" join
    ]
  }
} ;
