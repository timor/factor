USING: accessors choose-fail classes classes.algebra classes.tuple combinators
combinators.short-circuit kernel math parser sequences slots.private
terms.unification ;

IN: terms.match

! Transforms match-templates into matcher code
! Input: a literal structure
! Output: a quotation with effect ( term -- ) which generates bindings or fails

<PRIVATE
: same-class? ( obj1 obj2 -- ? )
    [ class-of ] same? ; inline
PRIVATE>

GENERIC: matcher* ( obj -- quot: ( term -- ) )
! NOTE: not doing direct comparison here because it could be a variable on the
! lhs of the match equation.
M: object matcher* [ match ] curry ;

M: sequence matcher*
    [ class-of ] keep
    [ length ] keep
    [ swap matcher*
      '[ _ swap nth @ ]
    ] map-index
    '[
        dup { [ class-of _ class= ] [ length _ = ] } 1&&
        [ _ cleave ] [ fail ] if ] ;

<PRIVATE
: slots-matcher ( specs -- quot )
    [ 2 + swap matcher*
      '[ _ slot @ ]
    ] map-index
    '[ _ cleave ] ;

: (and-match) ( specs -- quot )
    [ matcher* ] map
    [ cleave ] curry ;
PRIVATE>

! NOTE: depends on tuple layout
M: tuple matcher*
    [ class-of ]
    [ tuple-slots slots-matcher ] bi
    '[ dup class-of _ eq?
       _ [ fail ] if
    ] ;

: or-failing ( quot -- quot )
    [ [ fail ] unless ] compose ;

TUPLE: and-matcher
    patterns ;

M: and-matcher matcher*
    patterns>> (and-match) ;

C: <and-matcher> and-matcher

! callable escape-hatch
TUPLE: call-matcher
    quot ;

C: <call-matcher> call-matcher

M: call-matcher matcher* quot>> ;

! Tuple "template" match pattern
! NOTE: does not length check
! _T{ class slot slot... }
TUPLE: tuple-matcher
    class-pattern
    slot-patterns ;

C: <tuple-matcher> tuple-matcher

M: tuple-matcher matcher*
    [ class-pattern>> matcher* [ class-of ] prepose ]
    [ slot-patterns>> slots-matcher ] bi
    [ bi ] 2curry ;

! TODO: rest argument, sanity check on slot number
SYNTAX: _T{ \ } parse-until unclip-slice swap <tuple-matcher> suffix! ;

SYNTAX: ![ parse-quotation <call-matcher> suffix! ;

SYNTAX: ?[ parse-quotation or-failing <call-matcher> suffix! ;

DEFER: ) delimiter
SYNTAX: &( \ ) parse-until and-matcher boa suffix! ;
