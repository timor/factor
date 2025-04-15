USING: accessors combinators kernel persistent.disjoint-sets
persistent.hashtables shuffle ;

IN: terms.relations

TUPLE: term-relation < persistent-union-find
    { schema persistent-hash } ;

<PRIVATE
: puf>term-rel ( term-rel puf -- term-relation )
    swap
    [ { [ imap>> ]
      [ pami>> ]
      [ ranks>> ]
      [ parents>> ]
    } cleave ] [ schema>> ] bi*
    term-relation boa ; inline
PRIVATE>

! NOTE: depends on superclass layout!
M: term-relation equated
    dupdd call-next-method puf>term-rel ;

M: term-relation added-atom
    dupd call-next-method puf>term-rel ;
