USING: effects kernel words ;

IN: chr.factor.defs

GENERIC: defined-effect ( w -- effect )
M: word defined-effect stack-effect ;
M: \ call defined-effect drop
    ( ..a quot: ( ..a -- ..b ) -- ..b ) ;
M: \ dip defined-effect drop
    ( ..a x quot: ( ..a -- ..b ) -- ..b x ) ;
M: \ cond defined-effect drop
    ( ..a assoc -- ..b ) ;
