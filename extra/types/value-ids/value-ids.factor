USING: accessors arrays hash-sets kernel namespaces sequences sets types ;

IN: types.value-ids

! * Identity tags for value definition
! Basically ad-hoc atom types.  Kept in a dnf form.  Reflects the structure
! with which a value has been constrained.

TUPLE: value-id members ;
C: <value-id> value-id
INSTANCE: \ value-id domain

M: \ value-id unknown-type-value
    counter 1array >hash-set 1array <value-id> ;

M: \ value-id domain-intersect drop
    [ members>> ] bi@
    [ intersect ] cartesian-map concat members <value-id> ;

M: \ value-id domain-value-diverges?* drop
    members>> empty? ;

M: \ value-id pprint-domain-value* drop
    members>>
    [ members natural-sort [ number>string ] map "·" join ]
    map "|" join "(" ")" surround "#" prepend ;

M: \ value-id apply-class-declaration 2drop ;

! M: \ value-id class>domain-declaration drop length ?? <repetition> ;

M: \ value-id class>domain-value nip unknown-type-value ;
