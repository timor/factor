USING: io kernel namespaces formatting ;
IN: compiler.messages



: compiler-message ( string -- )
    "trace-compilation" get [ [ print flush ] with-global ] [ drop ] if ;

: format-compiler-message ( ..args format-string -- )
    sprintf compiler-message ; inline
