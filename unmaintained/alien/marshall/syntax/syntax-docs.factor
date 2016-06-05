! Copyright (C) 2009 Jeremy Hughes.
! See http://factorcode.org/license.txt for BSD license.
USING: help.markup help.syntax kernel quotations words
alien.inline alien.syntax effects alien.marshall
alien.marshall.structs strings sequences alien.inline.syntax ;
in: alien.marshall.syntax

HELP: CM-FUNCTION:
{ $syntax "CM-FUNCTION: return name args\n    body\n;" }
{ $description "Like " { $link postpone\ C-FUNCTION: } " but with marshalling "
    "of arguments and return values."
}
{ $examples
  { $example
    "USING: alien.inline.syntax alien.marshall.syntax prettyprint ;"
    "in: example"
    ""
    "C-library: exlib"
    ""
    "C-INCLUDE: <stdio.h>"
    "C-INCLUDE: <stdlib.h>"
    "CM-FUNCTION: char* sum_diff ( const-int a, const-int b, int* x, int* y )"
    "    *x = a + b;"
    "    *y = a - b;"
    "    char* s = (char*) malloc(sizeof(char) * 64);"
    "    sprintf(s, \"sum %i, diff %i\", *x, *y);"
    "    return s;"
    ";"
    ""
    ";C-LIBRARY"
    ""
    "8 5 0 0 sum_diff . . ."
    "3\n13\n\"sum 13, diff 3\""
  }
}
{ $see-also define-c-marshalled postpone\ C-FUNCTION: postpone\ M-FUNCTION: } ;

HELP: CM-STRUCTURE:
{ $syntax "CM-STRUCTURE: name fields ... ;" }
{ $description "Like " { $link postpone\ C-STRUCTURE: } " but with marshalling of fields. "
    "Defines a subclass of " { $link struct-wrapper } " a constructor, and slot-like accessor words."
}
{ $see-also postpone\ C-STRUCTURE: postpone\ M-STRUCTURE: } ;

HELP: M-FUNCTION:
{ $syntax "M-FUNCTION: return name args ;" }
{ $description "Like " { $link postpone\ FUNCTION: } " but with marshalling "
    "of arguments and return values."
}
{ $see-also marshalled-function postpone\ C-FUNCTION: postpone\ CM-FUNCTION: } ;

HELP: M-STRUCTURE:
{ $syntax "M-STRUCTURE: name fields ... ;" }
{ $description "Like " { $link postpone\ C-STRUCT: } " but with marshalling of fields. "
    "Defines a subclass of " { $link struct-wrapper } " a constructor, and slot-like accessor words."
}
{ $see-also define-marshalled-struct postpone\ C-STRUCTURE: postpone\ CM-STRUCTURE: } ;

HELP: define-c-marshalled
{ $values
    { "name" string } { "types" sequence } { "effect" effect } { "body" string }
}
{ $description "Defines a C function and a factor word which calls it with marshalling of "
    "args and return values."
}
{ $see-also define-c-marshalled' } ;

HELP: define-c-marshalled'
{ $values
    { "name" string } { "effect" effect } { "body" string }
}
{ $description "Like " { $link define-c-marshalled } ". "
     "The effect elements must be C type strings."
} ;

HELP: marshalled-function
{ $values
    { "name" string } { "types" sequence } { "effect" effect }
    { "word" word } { "quot" quotation } { "effect" effect }
}
{ $description "Defines a word which calls the named C function. Arguments, "
     "return value, and output parameters are marshalled and unmarshalled."
} ;

