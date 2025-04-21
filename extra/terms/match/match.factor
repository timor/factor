USING: accessors choose-fail classes classes.tuple combinators
combinators.short-circuit kernel lexer math parser quotations sequences
slots.private terms.unification.private ;

IN: terms.match

! Transforms match-templates into matcher code
! Input: a literal structure
! Output: a quotation with effect ( term -- ) which generates bindings or fails

GENERIC: matcher* ( obj -- quot: ( term -- ) )
! NOTE: not doing direct comparison here because it could be a variable on the
! lhs of the match equation.
M: object matcher* [ unif-closure ] curry ;

! NOTE: accepting all types of sequences here
M: sequence matcher*
    [ length ] keep
    [ swap matcher*
      '[ _ swap nth @ ]
    ] map-index
    '[
        dup { [ sequence? ] [ length _ = ] } 1&&
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

! NOTE: quotations are simply tests
M: callable matcher*
    '[ @ [ fail ] unless ] ;

TUPLE: and-match
    patterns ;

M: and-match matcher*
    patterns>> (and-match) ;

! allows reflexive access to the value being checked
! NOTE: this is just a special case for an and!
TUPLE: bind-match
    var
    pattern ;

M: bind-match matcher*
    [ var>> ]
    [ pattern>> matcher* ] bi
    '[ dup _ unif-closure
       @ ] ;

SYNTAX: As(
        scan-object
        scan-object
        ")" expect bind-match boa suffix! ;

! Tuple "template" match pattern
! NOTE: does not length check
! _T{ class slot slot... }
TUPLE: tuple-match
    class-pattern
    slot-patterns ;

! : <tuple-match> ( class slots -- obj )


M: tuple-match matcher*
    [ class-pattern>> ]
    [ slot-patterns>> slots-matcher ] bi
    '[ dup _ instance?
       _ [ fail ] if
    ] ;

! TODO: rest argument, sanity check on slot number
SYNTAX: _T{ scan-class \ } parse-until tuple-match boa suffix! ;

DEFER: ) delimiter
SYNTAX: &( \ ) parse-until and-match boa suffix! ;
