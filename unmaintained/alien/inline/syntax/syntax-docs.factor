! Copyright (C) 2009 Jeremy Hughes.
! See http://factorcode.org/license.txt for BSD license.
USING: help.markup help.syntax alien.inline ;
in: alien.inline.syntax

HELP: ;C-LIBRARY
{ $syntax ";C-LIBRARY" }
{ $description "Writes, compiles, and links code generated since previous invocation of " { $link postpone: C-library: } "." }
{ $see-also postpone: compile-c-library } ;

HELP: C-FRAMEWORK:
{ $syntax "C-FRAMEWORK: name" }
{ $description "OS X only. Link to named framework. Takes effect when " { $link postpone: ;C-LIBRARY } " is called." }
{ $see-also postpone: c-use-framework } ;

HELP: C-FUNCTION:
{ $syntax "C-FUNCTION: return name ( args ... )\nbody\n;" }
{ $description "Appends a function to the C library in scope and defines an FFI word that calls it." }
{ $examples
  { $example
    "USING: alien.inline.syntax prettyprint ;"
    "in: cmath.ffi"
    ""
    "C-library: cmathlib"
    ""
    "C-FUNCTION: int add ( int a, int b )"
    "    return a + b;"
    ";"
    ""
    ";C-LIBRARY"
    ""
    "1 2 add ."
    "3" }
}
{ $see-also postpone: define-c-function } ;

HELP: C-INCLUDE:
{ $syntax "C-INCLUDE: name" }
{ $description "Appends an include line to the C library in scope." }
{ $see-also postpone: c-include } ;

HELP: C-library:
{ $syntax "C-library: name" }
{ $description "Starts a new C library scope. Other " { $snippet "alien.inline" } " syntax can be used after this word." }
{ $examples
  { $example
    "USING: alien.inline.syntax ;"
    "in: rectangle.ffi"
    ""
    "C-library: rectlib"
    ""
    "C-STRUCTURE: rectangle { \"int\" \"width\" } { \"int\" \"height\" } ;"
    ""
    "C-FUNCTION: int area ( rectangle c )"
    "    return c.width * c.height;"
    ";"
    ""
    ";C-LIBRARY"
    "" }
}
{ $see-also postpone: define-c-library } ;

HELP: C-LINK/FRAMEWORK:
{ $syntax "C-LINK/FRAMEWORK: name" }
{ $description "Equivalent to " { $link postpone: C-FRAMEWORK: } " on OS X and " { $link postpone: C-LINK: } " everywhere else." }
{ $see-also postpone: c-link-to/use-framework } ;

HELP: C-LINK:
{ $syntax "C-LINK: name" }
{ $description "Link to named library. Takes effect when " { $link postpone: ;C-LIBRARY } " is called." }
{ $see-also postpone: c-link-to } ;

HELP: C-STRUCTURE:
{ $syntax "C-STRUCTURE: name pairs ... ;" }
{ $description "Like " { $snippet "C-STRUCT:" } " but also generates equivalent C code."}
{ $see-also postpone: define-c-struct } ;

HELP: C-TYPEDEF:
{ $syntax "C-TYPEDEF: old new" }
{ $description "Like " { $snippet "TYPEDEF:" } " but generates a C typedef statement too." }
{ $see-also postpone: define-c-typedef } ;

HELP: COMPILE-AS-C++
{ $syntax "COMPILE-AS-C++" }
{ $description "Insert this word anywhere between " { $link postpone: C-library: } " and " { $link postpone: ;C-LIBRARY } " and the generated code will be treated as C++ with " { $snippet "extern \"C\"" } " prepended to each function prototype." } ;

HELP: DELETE-C-library:
{ $syntax "DELETE-C-library: name" }
{ $description "Deletes the shared library file corresponding to " { $snippet "name" } " . " }
{ $notes
  { $list
    { "Must be executed in the vocabulary where " { $snippet "name" } " is defined. " }
    "This word is mainly useful for unit tests."
  }
}
{ $see-also postpone: delete-inline-library } ;

HELP: <RAW-C
{ $syntax "<RAW-C code RAW-C>" }
{ $description "Insert a (multiline) string into the generated source file. Useful for macros and other details not implemented in " { $snippet "alien.inline" } "." } ;
