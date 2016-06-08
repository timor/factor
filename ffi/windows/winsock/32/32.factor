USING: alien.c-types classes.struct ;
in: windows.winsock.32

STRUCT: servent
    { name c-string }
    { aliases void* }
    { port short }
    { proto c-string } ;
