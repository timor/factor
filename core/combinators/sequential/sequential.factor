USING: combinators.smart generalizations kernel sequences sequences.cords ;

IN: combinators.sequential

:: with-prev* ( quot: ( ..a elt -- ..b ) initial -- quot: ( ..a prev elt -- ..b ) )
    initial :> last! [ [ last swap ] quot compose keep last! ] ; inline

SINGLETON: +start+
SINGLETON: +end+

: with-prev ( quot: ( ..a elt -- ..b ) -- quot: ( ..a prev elt -- ..b ) )
    +start+ with-prev* ; inline

<PRIVATE
: nopping ( quot dummy -- quot )
    [ [ dropping ] [ outputs ] bi ] dip swap
    '[ _ _ dupn ] compose ; inline
PRIVATE>

: skip-start ( quot: ( ..a prev elt -- ..b ) default -- quot: ( ..a prev elt -- ..b ) )
    [ nopping ] keepd '[ over +start+? _ _ if ] ; inline

: with-next* ( seq quot: ( ..a elt -- ..b ) initial -- seq quot: ( ..a prev elt -- ..b ) )
    [ { +end+ } cord-append ] 2dip with-prev* ; inline

: with-next ( seq quot: ( ..a elt -- ..b ) -- seq quot: ( ..a prev elt -- ..b ) )
    [ unclip-slice ] dip swap with-next* ; inline

: skip-end ( quot: ( ..a prev elt -- ..b ) default -- quot: ( ..a prev elt -- ..b ) )
    [ nopping ] keepd '[ dup +end+? _ _ if ] ; inline

:: with-feedback ( quot: ( ..a eltN -- ..b eltN+1 ) elt0 -- quot: ( ..a eltN-1 eltN -- ..b eltN+1 ) )
    elt0 :> last! [ last swap quot call last! ] ; inline
