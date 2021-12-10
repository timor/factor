USING: accessors kernel math quotations sequences sequences.private ;

IN: types.util

TUPLE: mapped
    { seq sequence read-only }
    { at-quot maybe{ callable } read-only } ;

C: <mapped> mapped

INSTANCE: mapped immutable-sequence
M: mapped length seq>> length ;
M: mapped nth-unsafe
    [ seq>> nth-unsafe ]
    [ at-quot>> call( elt -- elt ) ] bi ;

! Like 2map, but will return prefix of longer sequence prepended
! 2map ( ... seq1 seq2 quot: ( ... elt1 elt2 -- ... newelt ) -- ... newseq )

: 2map-suffix ( ... seq1 seq2 quot: ( ... elt1 elt2 -- ... newelt ) -- ... newseq )
    [
        2dup longer? [ swap ] when
        2dup [ length ] bi@ swap -
        cut-slice swap
    ] dip swap
    [ 2map ] dip prepend ; inline
