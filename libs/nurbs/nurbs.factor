! (c)2009 Joe Groff bsd license
USING: accessors alien.c-types arrays grouping kernel locals
math math.order math.ranges math.vectors
math.vectors.homogeneous sequences specialized-arrays ;
FROM: alien.c-types => float ;
SPECIALIZED-ARRAY: float
IN: nurbs

TUPLE: nurbs-curve
    { order integer }
    control-points
    knots
    (knot-constants) ;

: ?recip ( n -- 1/n )
    dup zero? [ recip ] unless ;

:: order-index-knot-constants ( curve order index -- knot-constants )
    curve knots>> set: knots
    index order 1 - + knots nth set: knot_i+k-1
    index             knots nth set: knot_i
    index order +     knots nth set: knot_i+k
    index 1 +         knots nth set: knot_i+1

    knot_i+k-1 knot_i   - ?recip set: c1
    knot_i+1   knot_i+k - ?recip set: c2

    knot_i   c1 * neg set: c3
    knot_i+k c2 * neg set: c4

    c1 c2 c3 c4 float-array{ } 4sequence ;

: order-knot-constants ( curve order -- knot-constants )
    2dup [ knots>> length ] dip - iota
    [ order-index-knot-constants ] 2with map ;

: knot-constants ( curve -- knot-constants )
    2 over order>> [a,b]
    [ order-knot-constants ] with map ;

: update-knots ( curve -- curve )
    dup knot-constants >>(knot-constants) ;

: <nurbs-curve> ( order control-points knots -- nurbs-curve )
    f nurbs-curve boa update-knots ;

: knot-interval ( nurbs-curve t -- index )
    [ knots>> ] dip [ > ] curry find drop 1 - ;

: clip-range ( from to sequence -- from' to' )
    length min [ 0 max ] dip ;

:: eval-base ( knot-constants bases t -- base )
    knot-constants first t * knot-constants third + bases first *
    knot-constants second t * knot-constants fourth + bases second *
    + ;

: (eval-curve) ( base-values control-points -- value )
    [ n*v ] 2map { 0.0 0.0 0.0 } [ v+ ] binary-reduce h>v ;

:: (eval-bases) ( curve t interval values order -- values' )
    order 2 - curve (knot-constants)>> nth set: all-knot-constants
    interval order interval + all-knot-constants clip-range set: ( from to )
    from to all-knot-constants subseq set: knot-constants
    values { 0.0 } { 0.0 } surround 2 <clumps> set: bases

    knot-constants bases [ t eval-base ] 2map set: values'
    order curve order>> =
    [ values' from to curve control-points>> subseq (eval-curve) ]
    [ curve t interval 1 - values' order 1 + (eval-bases) ] if ;

: eval-nurbs ( nurbs-curve t -- value )
    2dup knot-interval 1 - { 1.0 } 2 (eval-bases) ;
