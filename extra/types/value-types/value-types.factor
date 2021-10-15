USING: accessors arrays classes effects formatting kernel lists math.parser
sequences terms types.algebra types.base-types types.function-types types.util ;

IN: types.value-types
! * Value level types

! Value level types are all factor classes and user-defined parametric types
! ** Literal wrappers
TUPLE: literal-value value ;
C: <literal-value> literal-value
INSTANCE: literal-value proper-term
M: literal-value args>> drop f ;
M: literal-value effect>string value>> spprint "'" dup surround ;
M: object effect-element>term <literal-value> ;
M: literal-value term-value-type value>> class-of ;

! ** Deferred Computation results
! Representing a combinator?
TUPLE: lazy-computation word inputs ;
C: <lazy-computation> lazy-computation
INSTANCE: lazy-computation proper-term
M: lazy-computation args>>
    inputs>> ;
M: lazy-computation from-args*
    word>> swap <lazy-computation> ;
M: lazy-computation effect>string
    [ word>> name>> ]
    [ inputs>> [ effect>string ] map " " join "(" ")" surround append ] bi
    "[" "]" surround ;
M: lazy-computation instantiate-term ;
: foldable-computation? ( lazy-computation -- ? )
    { [ word>> foldable? ]
        [ inputs>> [ literal-value? ] all? ]
    } 1&& ;
: maybe-fold-lazy-computation ( lazy-computation -- lazy-computation/array ? )
    dup foldable-computation?
    [ [ inputs>> [ value>> ] map ] [ word>> 1quotation ] bi with-datastack
      [ <literal-value> ] map
      t ]
    [ f ] if ;
M: lazy-computation simplify-term*
    call-next-method
    maybe-fold-lazy-computation swap [ or ] dip ;


TUPLE: eval-result n { result union{ sequence lazy-computation } } ;
! TUPLE: eval-result n result ;
INSTANCE: eval-result proper-term
C: <eval-result> eval-result
M: eval-result args>> result>> 1array ;
M: eval-result from-args* n>> swap first <eval-result> ;
M: eval-result effect>string
    [ result>> effect>string ] [ n>> ] bi number>subscript append ;
M: eval-result instantiate-term ;
M: eval-result term-value-type
    [ n>> ] [ result>> word>> stack-effect effect-out-types ] bi nth ;
M: eval-result simplify-term*
    call-next-method
    dup result>> lazy-computation?
    [ [ n>> ] [ result>> ] bi nth [ drop t ] dip ] unless ;

! ** Value types
! Place holder for value-level computations.
! This actually inverts the relation between types and values, kind of.
TUPLE: value-type type value ;
C: <value-type> value-type
INSTANCE: value-type proper-term
M: value-type effect>string
    [ type>> effect>string ]
    [ value>> effect>string ] bi ":" glue
    "⟨" "⟩" surround ;
M: value-type term-value-type
    type>> term-value-type ;

! ! * Protocol types
! TUPLE: assoc-type history ;
! INSTANCE: assoc-type proper-term
! C: <assoc-type> assoc-type

! TUPLE: assoc-set-record key value ;
! C: <assoc-set> assoc-set-record
! INSTANCE: assoc-set-record proper-term

! ! Effect-level, e.g. template
! : set-assoc-type ( key value -- type )
!     <assoc-set> "R" cons
!     <assoc-type> ;

! * Connecting to term types


! M: annotated-type-var
