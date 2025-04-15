USING: accessors assocs kernel math namespaces vocabs words ;

IN: terms.util

! Words that should be defined in other vocabs...

: unintern ( word -- )
    [ [ f ] change-vocabulary
      name>> swap vocab-words-assoc delete-at ] keep
    [ \ <uninterned-word> counter >fixnum ] dip hashcode<< ;

: >subscript ( str -- str )
    [ H{ { CHAR: 1 CHAR: ₁ }
       { CHAR: 2 CHAR: ₂ }
       { CHAR: 3 CHAR: ₃ }
       { CHAR: 4 CHAR: ₄ }
       { CHAR: 5 CHAR: ₅ }
       { CHAR: 6 CHAR: ₆ }
       { CHAR: 7 CHAR: ₇ }
       { CHAR: 8 CHAR: ₈ }
       { CHAR: 9 CHAR: ₉ }
       { CHAR: 0 CHAR: ₀ }
       } ?at drop ] map ;
