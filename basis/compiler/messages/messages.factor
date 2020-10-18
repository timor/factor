USING: combinators formatting fry io kernel macros math namespaces ;
IN: compiler.messages

: trace-level ( -- f/number )
    "trace-compilation" get { { t [ 1 ] } { f [ 0 ] } [  ] } case ;
    ! [ dup number? [ drop 0 ] unless ] when ;

: print-compiler-message ( string -- )
    "trace-compilation" get [ [ print flush ] with-global ] [ drop ] if ;

: compiler-message* ( string level -- )
    trace-level <= [ print-compiler-message ] [ drop ] if ;

: compiler-message ( string -- )
    1 compiler-message* ;

MACRO: format-compiler-message ( format-string level -- quot )
    '[ _ sprintf _ compiler-message* ] ;
