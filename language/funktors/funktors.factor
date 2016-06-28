! Copyright (C) 2016 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors arrays effects.parser eval interpolate
io.streams.string kernel locals.parser namespaces parser
sequences words ;
IN: funktors

SYNTAX: \ FUNKTOR:
    scan-new-escaped
    scan-effect dup in>> [ dup pair? [ first ] when ] map make-locals
    drop [ name>> ] map reverse [ $[ _ namespaces:set ] ] map [ ] [ compose ] reduce
    scan-object interpolate-locals-quot compose
    $[ [ _ call ] with-string-writer eval-in-current( -- ) ] swap define-declared ;
    ! $[ @ interpolate>string eval-in-current( -- ) ] swap define-declared ;