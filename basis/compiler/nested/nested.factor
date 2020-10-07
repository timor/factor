USING: accessors arrays assocs compiler continuations debugger formatting io
kernel namespaces sequences summary words ;

IN: compiler.nested

SYMBOL: nested-compilation?
nested-compilation? [ f ] initialize

! Store a trace to detect cycles when compiling nested words
SYMBOL: nested-compilations

! List of words passed to recompile
SYMBOL: recompile-set

! If a nested compilation updated the `compiled` hashtable already, don't do anything
: maybe-compile-word ( word -- )
    dup compiled get key?
    [ drop ]
    [
        [ 1array nested-compilations namespaces:set ]
        [ compile-word ] bi
    ] if ;

ERROR: nested-compilation-cycle word trace ;
M: nested-compilation-cycle summary
    [ word>> ] [ trace>> ] bi "Compilation cycle for %s: %u" sprintf ;

ERROR: deferred-word-call word trace ;
M: deferred-word-call summary
    [ word>> ] [ trace>> ] bi "Trying to compile call to deferred word: %s. Trace: %u" sprintf ;


: in-nested-compilation? ( word -- ? )
    nested-compilations get member? ;

: nested-compile ( word -- )
    dup name>> "Trying nested compile: %s" sprintf compiler-message
    dup deferred? [ nested-compilations get deferred-word-call ] when
    dup in-nested-compilation?
    [ nested-compilations get nested-compilation-cycle ]
    [ [
            [ nested-compilations [ swap suffix ] change ]
            [ compile-word ] bi
        ] with-scope ] if ;

: try-nested-compile ( word -- ? )
    dup [ compile? ] [ recompile-set get member? ] bi and
    nested-compilation? get and
    [ nested-compile t ]
    [ drop f ] if ;

: nested-compilation-message ( -- )
    nested-compilations get "nested trace: %[%s, %]\n" sprintf compiler-message ;

<<
"compiling safe-nested-compile" print flush ! This should go to stderr!
: safe-nested-compile ( word -- ? )
    [ try-nested-compile ] [ dup nested-compilation-cycle? [ error. flush drop f ] [ rethrow ] if ] recover ;
>>
