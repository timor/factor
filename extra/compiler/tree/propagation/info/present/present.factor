USING: accessors arrays classes.algebra combinators
compiler.tree.propagation.info formatting kernel locals math math.functions
math.intervals present sequences words ;
IN: compiler.tree.propagation.info.present


! * Presenting Value info

: interval-finite? ( int -- ? )
    interval-length 1/0. = not ;

PREDICATE: number-info < value-info-state class>> number class<= ;
PREDICATE: integer-info < number-info class>> integer class<= ;
PREDICATE: float-info < number-info class>> float class<= ;
PREDICATE: ratio-info < number-info class>> ratio class<= ;
PREDICATE: fixint-info < integer-info interval>> interval-finite? ;
PREDICATE: uint-info < fixint-info interval>> interval-nonnegative? ;
PREDICATE: sequence-info < value-info-state class>> sequence class<= ;
PREDICATE: word-info < value-info-state class>> word class<= ;

GENERIC: interval-label ( interval -- str )
GENERIC: class-label ( info -- str )

: log2-point ( x -- str )
    { { [ dup 0 = ] [ ] }
      { [ dup neg? ] [ abs 2 logn "-2^%.1f" sprintf ] }
      [ 2 logn "2^%.1f" sprintf ]
    } cond ;

:: points-label ( from to -- str )
    from second "[" "(" ?
                      from first dup -1/0. = [ drop "-∞" ] [ log2-point ] if
                      to first dup 1/0. = [ drop "∞" ] [ log2-point ] if
                      to second "]" ")" ?
    "%s%s,%s%s" sprintf ;
M: empty-interval interval-label drop "∅" ;
M: full-interval interval-label drop f ;
M: interval interval-label interval>points points-label ;

M: number-info class-label drop "ℕ" ;
M: integer-info class-label drop "ℤ" ;
M: float-info class-label drop "ℝ" ;
M: ratio-info class-label drop "ℚ" ;
M: uint-info class-label drop "ℤ₀⁺" ;
M: object class-label drop "𝕌" ;
M: sequence-info class-label class>>
    dup word?
    [ name>> "{" "}" surround ]
    [ "{%u}" sprintf ] if ;
M: word-info class-label drop "𝕎" ;

: (interval-label) ( info -- str )
    { { [ dup not ] [ drop "?" ] }
      { [ dup literal?>> ] [ literal>> identity-hashcode 0x10000 mod "#%x" sprintf ] }
      [ interval>> interval-label ] } cond ;

: value-info-label ( info -- str/f )
    [ [ class-label ] [ (interval-label) ] bi 2array sift ":" join ]
    [ "" ] if* ;

M: value-info-state present
    value-info-label "f" or ;
