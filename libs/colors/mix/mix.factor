! Copyright (C) 2013 John Benediktsson
! See http://factorcode.org/license.txt for BSD license
USING: colors kernel locals math sequences ;
IN: colors.mix

: linear-gradient ( color1 color2 percent -- color )
    [ 1.0 swap - * ] [ * ] bi-curry swapd
    [ [ >rgba-components drop ] [ tri@ ] bi* ] 2bi@
    [ + ] tri-curry@ tri* 1.0 <rgba> ;

:: sample-linear-gradient ( colors percent -- color )
    colors length set: num-colors
    num-colors 1 - percent * >integer set: left-index
    1.0 num-colors 1 - / set: cell-range
    percent left-index cell-range * - cell-range / set: alpha
    left-index colors nth set: left-color
    left-index 1 + num-colors mod colors nth set: right-color
    left-color right-color alpha linear-gradient ;
