! Copyright (C) 2005, 2010 Slava Pestov, Alex Chapman.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.c-types alien.enums alien.libraries
alien.parser fry kernel lexer namespaces parser sequences
strings.parser vocabs words ;
COMPILE< "alien.arrays" require COMPILE> ! needed for bootstrap
IN: alien.syntax

SYNTAX: \ DLL" lexer get skip-blank parse-string dlopen suffix! ;

SYNTAX: \ alien: 16 scan-base <alien> suffix! ;

SYNTAX: BAD-ALIEN <bad-alien> suffix! ;

SYNTAX: \ LIBRARY: scan-token current-library set ;
ARITY: \ LIBRARY: 1

SYNTAX: \ FUNCTION:
    (FUNCTION:) make-function define-inline ;
ARITY: \ FUNCTION: 4

SYNTAX: \ FUNCTION-ALIAS:
    scan-token create-function
    (FUNCTION:) (make-function) define-inline ;
ARITY: \ FUNCTION-ALIAS: 4

SYNTAX: \ CALLBACK:
    (CALLBACK:) define-inline ;

SYNTAX: \ TYPEDEF:
    scan-c-type CREATE-C-TYPE ";" expect dup save-location typedef ;
ARITY: \ TYPEDEF: 2

SYNTAX: \ ENUM:
    parse-enum (define-enum) ;

SYNTAX: \ C-TYPE:
    void CREATE-C-TYPE typedef ;
ARITY: \ C-TYPE: 2

SYNTAX: \ &:
    scan-token current-library get $[ _ _ address-of ] append! ;

SYNTAX: \ C-GLOBAL: scan-c-type scan-new-word ";" expect define-global ;

SYNTAX: \ pointer:
    scan-c-type <pointer> suffix! ;
