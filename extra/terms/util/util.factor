USING: accessors assocs kernel math namespaces vocabs words ;

IN: terms.util

! Words that should be defined in other vocabs...

: unintern ( word -- )
    [ [ f ] change-vocabulary
      name>> swap vocab-words-assoc delete-at ] keep
    [ \ <uninterned-word> counter >fixnum ] dip hashcode<< ;
