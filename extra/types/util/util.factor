USING: accessors kernel quotations sequences sequences.private ;

IN: types.util

TUPLE: mapped
    { seq sequence read-only }
    { at-quot maybe{ callable } read-only } ;

C: <mapped> mapped

INSTANCE: mapped immutable-sequence
M: mapped length seq>> length ;
M: mapped nth-unsafe
    [ seq>> nth-unsafe ]
    [ at-quot>> call( elt -- elt ) ] bi ;
