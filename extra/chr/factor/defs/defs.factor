USING: effects kernel words ;

IN: chr.factor.defs

GENERIC: defined-effect ( w -- effect )
M: word defined-effect stack-effect ;
M: \ call defined-effect drop
    ( ..a quot: ( ..a -- ..b ) -- ..b ) ;
