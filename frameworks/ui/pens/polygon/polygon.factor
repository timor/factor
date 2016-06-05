! Copyright (C) 2009 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors alien.c-types alien.data colors help.markup
help.syntax kernel opengl opengl.gl sequences math.vectors
ui.gadgets ui.pens specialized-arrays ;
specialized-array: float
in: ui.pens.polygon

! Polygon pen
TUPLE: polygon color
interior-vertices
interior-count
boundary-vertices
boundary-count ;

: close-path ( points -- points' )
    dup first suffix ;

: <polygon> ( color points -- polygon )
    dup close-path [ [ concat float >c-array ] [ length ] bi ] bi@
    polygon boa ;

M: polygon draw-boundary
    nip
    [ color>> gl-color ]
    [ boundary-vertices>> gl-vertex-pointer ]
    [ [ GL_LINE_STRIP 0 ] dip boundary-count>> glDrawArrays ]
    tri ;

M: polygon draw-interior
    nip
    [ color>> gl-color ]
    [ interior-vertices>> gl-vertex-pointer ]
    [ [ GL_POLYGON 0 ] dip interior-count>> glDrawArrays ]
    tri ;

: <polygon-gadget> ( color points -- gadget )
    [ <polygon> ] [ max-dims ] bi
    [ <gadget> ] 2dip [ >>interior ] [ >>dim ] bi* ;