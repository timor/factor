USING: persistent.disjoint-sets persistent.hashtables ;

IN: terms.relations

TUPLE: term-relation < persistent-union-find
    { schema persistent-hash } ;
