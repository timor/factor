USING: continuations namespaces tools.deploy.shaker ;
in: debugger

: error. ( error -- ) original-error get die-with2 ;

: print-error ( error -- ) error. ;
