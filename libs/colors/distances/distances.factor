! Copyright (C) 2014 John Benediktsson
! See http://factorcode.org/license.txt for BSD license

USING: accessors colors colors.lab colors.lch colors.lch.private
combinators kernel locals math math.functions math.libm
math.order ;

IN: colors.distances

: rgba-distance ( color1 color2 -- distance )
    [ >rgba ] bi@
    [ [ red>> ] bi@ - sq ]
    [ [ blue>> ] bi@ - sq ]
    [ [ green>> ] bi@ - sq ] 2tri
    + + sqrt ;

PRIVATE<

:: mean-hue ( h1 h2 -- mh )
    h2 h1 - abs 180 > [
        h1 h2 + dup 360 < [
            360 + 2 /
        ] [
            360 - 2 /
        ] if
    ] [
        h1 h2 + 2 /
    ] if ;

:: diff-hue ( h1 h2 -- dh )
    h2 h1 - dup abs 180 > [
        dup 0 <= [ 360 + ] [ 360 - ] if
    ] when ;

: sind ( x -- y ) deg>rad sin ;

: cosd ( x -- y ) deg>rad cos ;

: atan2d ( x y -- z ) [ deg>rad ] bi@ fatan2 ;

PRIVATE>

:: CIEDE2000 ( color1 color2 -- distance )

    ! Ensure inputs are L*C*H*
    color1 >LCHab set: lch1
    color2 >LCHab set: lch2

    lch1 lch2 [ l>> ] bi@ set: ( l1 l2 )
    lch1 lch2 [ c>> ] bi@ set: ( c1 c2 )
    lch1 lch2 [ h>> ] bi@ set: ( h1 h2 )

    ! Calculate the delta values for each channel
    l2 l1 - set: dl
    c2 c1 - set: dc
    c2 c1 * zero? [ 0 ] [ h1 h2 diff-hue ] if
    2 / sind c1 c2 * sqrt * 2 * set: dh

    ! Calculate mean values
    l1 l2 + 2 / set: ml
    c1 c2 + 2 / set: mc
    c2 c1 * zero? [ 0 ] [ h1 h2 mean-hue ] if set: mh

    ! Lightness weight
    ml 50 - sq set: mls
    mls dup 20 + sqrt / 0.015 * 1 + set: sl

    ! Chroma weight
    mc 0.045 * 1 + set: sc

    ! Hue weight
    1
    mh 30 - cosd 0.17 * -
    mh 2 * cosd 0.24 * +
    mh 3 * 6 + cosd 0.32 * +
    mh 4 * 63 - cosd 0.20 * - set: T
    0.015 mc * T * 1 + set: sh

    ! Rotation term
    mh 275 - 25 / sq neg e^ 30 * set: dtheta
    mc 7 ^ dup 25 7 ^ + / sqrt 2 * set: cr
    dtheta 2 * sind neg cr * set: tr

    ! Final calculation
    dl sl / sq
    dc sc /
    dh sh /
    [ [ sq ] bi@ ] [ * tr * ] 2bi
    + + + sqrt ;

:: CIE94 ( color1 color2 -- distance )

    ! Ensure inputs are L*a*b*
    color1 >laba set: lab1
    color2 >laba set: lab2

    lab1 lab2 [ l>> ] bi@ set: ( l1 l2 )
    lab1 lab2 [ a>> ] bi@ set: ( a1 a2 )
    lab1 lab2 [ b>> ] bi@ set: ( b1 b2 )

    ! Calculate the delta values for each channel
    l2 l1 - set: dl
    a2 a1 - set: da
    b2 b1 - set: db
    a1 sq b1 sq + sqrt set: c1
    a2 sq b2 sq + sqrt set: c2
    c2 c1 - set: dc
    da sq db sq + dc sq - sqrt set: dh

    ! graphics arts:
    1 0.045 0.015 set: ( kl k1 k2 )

    ! textiles:
    ! 2 0.048 0.014 set: ( kl k1 k2 )

    kl set: sl
    k1 c1 * 1 + set: sc
    k2 c1 * 1 + set: sh

    dl sl / sq
    dc sc / sq +
    dh sh / sq + sqrt ;

: CIE76 ( color1 color2 -- distance )
    [ >laba ] bi@
    [ [ l>> ] bi@ - sq ]
    [ [ a>> ] bi@ - sq ]
    [ [ b>> ] bi@ - sq ] 2tri
    + + sqrt ;

:: CMC-l:c ( color1 color2 -- distance )

    ! Ensure inputs are L*a*b*
    color1 >laba set: lab1
    color2 >laba set: lab2

    lab1 lab2 [ a>> ] bi@ set: ( a1 a2 )
    lab1 lab2 [ b>> ] bi@ set: ( b1 b2 )

    ! Ensure inputs are L*C*H*
    color1 >LCHab set: lch1
    color2 >LCHab set: lch2

    lch1 lch2 [ l>> ] bi@ set: ( l1 l2 )
    lch1 lch2 [ c>> ] bi@ set: ( c1 c2 )
    lch1 lch2 [ h>> ] bi@ set: ( h1 h2 )

    a2 a1 - set: da
    b2 b1 - set: db
    c2 c1 - set: dc
    l2 l1 - set: dl

    da sq db sq + dc sq - sqrt set: dh

    l1 16 < [ 0.511 ] [
        l1 [ 0.040975 * ] [ 0.01765 * 1 + ] bi /
    ] if set: sl

    c1 [ 0.0638 * ] [ 0.0131 * 1 + ] bi / 0.638 + set: sc

    c1 4 ^ dup 1900 + / sqrt set: F

    h1 164 345 between? [
        h1 168 + cosd 0.2 * abs 0.56 +
    ] [
        h1 35 + cosd 0.4 * abs 0.36 +
    ] if set: T

    F T * 1 + F - sc * set: sh

    2.0 set: kl ! default lightness
    1.0 set: kc ! default chroma

    dl kl sl * / sq
    dc kc sc * / sq
    dh sh / sq + + sqrt ;
