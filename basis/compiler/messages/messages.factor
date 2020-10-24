USING: calendar calendar.format combinators combinators.smart formatting
formatting.private fry generalizations io io.encodings.utf8 io.files kernel
io.pathnames prettyprint.config
macros math namespaces sequences ;
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

SYMBOL: compilation-trace-file

: make-trace-file ( path -- filename )
   "compilation-trace-" now timestamp>mdtm append append-path ;

: with-trace-file-output ( quot -- )
    compilation-trace-file get [ utf8 rot [ nl ] compose [ without-limits ] curry with-file-appender ] [ inputs ndrop ] if* ; inline

: print-to-trace-file ( string -- )
    ! compilation-trace-file get [ utf8 [ print ] with-file-writer ] [ drop ] if* ;
    [ write ] with-trace-file-output ;

: start-trace-file ( -- )
    "Compilation Trace started: " now timestamp>string append print-to-trace-file ;

MACRO: format-to-trace-file ( format-string -- quot )
    printf-quot '[
        [ @ output-stream get [ stream-write ] curry _ napply ] with-trace-file-output
    ] ;
