USING: alien.c-types classes.struct ;
in: windows.winsock.64

STRUCT: servent
    { name c-string }
    { aliases void* }
    { proto c-string }
    { port short } ;
