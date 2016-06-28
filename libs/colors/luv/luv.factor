! Copyright (C) 2014 John Benediktsson
! See http://factorcode.org/license.txt for BSD license

USING: accessors colors colors.xyz colors.xyz.private kernel
locals math math.functions ;

IN: colors.luv

TUPLE: luva l u v alpha ;

C: <luva> luva

PRIVATE<

:: xyz-to-uv ( x y z -- u v )
    x y 15 * z 3 * + + set: d
    4 x * d /
    9 y * d / ; foldable

PRIVATE>

M: luva >rgba >xyza >rgba ;

M: luva >xyza
    [
        let[
            wp_x wp_y wp_z xyz-to-uv set: ( u_wp v_wp )
            [ l>> ] [ u>> ] [ v>> ] tri set: ( l u v )

            52 l * 13 l * u_wp * u + / 1 - 3 / set: a
            l xyz_kappa xyz_epsilon * > [
                l 16 + 116 / 3 ^ wp_y *
            ] [
                l xyz_kappa / wp_y *
            ] if set: y
            y -5 * set: b
            39 l * 13 l * v_wp * v + / 5 - y * set: d
            d b - a 1/3 + / set: x
            a x * b + set: z

            x y z
        ]
    ] [ alpha>> ] bi <xyza> ;

GENERIC: >luva ( color -- luva )

M: object >luva >rgba >luva ;

M: rgba >luva >xyza >luva ;

M: luva >luva ; inline

M: xyza >luva
    [
        let[
            wp_x wp_y wp_z xyz-to-uv set: ( u_wp v_wp )
            [ x>> ] [ y>> ] [ z>> ] tri set: ( x_ y_ z_ )
            x_ y_ z_ xyz-to-uv set: ( u_ v_ )

            y_ wp_y / set: y

            y xyz_epsilon > [
                y 1/3 ^ 116 * 16 -
            ] [
                xyz_kappa y *
            ] if set: l
            13 l * u_ u_wp - * set: u
            13 l * v_ v_wp - * set: v

            l u v
        ]
    ] [ alpha>> ] bi <luva> ;
