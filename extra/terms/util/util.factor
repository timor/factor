USING: accessors assocs kernel vocabs ;

IN: terms.util

! Words that should be defined in other vocabs...

: unintern ( word -- )
    dup vocabulary>> [ [ name>> ] dip vocab-words-assoc delete-at ] keepd
    f >>vocabulary drop ;
