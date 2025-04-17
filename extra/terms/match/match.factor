USING: accessors choose-fail classes classes.tuple combinators
combinators.short-circuit kernel lexer math parser sequences slots.private terms
terms.unification.private ;

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

! NOTE: depends on tuple layout
M: tuple matcher*
    [ class-of ]
    [ tuple-slots ] bi
    [ 2 + swap matcher*
      '[ _ slot @ ]
    ] map-index
    '[ dup class-of _ eq?
      [ _ cleave ]
      [ fail ] if
    ] ;

! NOTE: quotations are simply tests
M: callable matcher*
    '[ _ [ fail ] unless ] ;

! allows reflexive access to the value being checked
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
