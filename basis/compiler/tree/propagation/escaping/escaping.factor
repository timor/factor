USING: arrays disjoint-sets kernel namespaces sequences sets ;

IN: compiler.tree.propagation.escaping

FROM: namespaces => set ;

! * Tracking escaping values
! Taken from escape analysis, because we do this the moment we introduce values in copy

SYMBOL: +escaping+

: <escaping-values> ( -- disjoint-set )
    <disjoint-set> +escaping+ over add-atom ;

SYMBOL: escaping-values
! Init for bootstrapping
escaping-values [ <escaping-values> ] initialize

SYMBOL: inner-escaping-values
: record-inner-escaping-value ( value -- )
    inner-escaping-values get [ adjoin ] [ drop ] if* ;

SYMBOL: inner-equal-values
: record-inner-equal-values ( values -- )
    inner-equal-values get [ adjoin ] [ drop ] if* ;

: init-escaping-values ( -- )
    <escaping-values> escaping-values set ;

: (introduce-escaping-value) ( values escaping-values -- )
    2dup disjoint-set-member?
    [ 2drop ] [ add-atom ] if ; inline

: introduce-escaping-value ( value -- )
    escaping-values get [ (introduce-escaping-value) ] [ drop ] if* ;

: introduce-escaping-values ( values -- )
    escaping-values get dup
    [ '[ _ (introduce-escaping-value) ] each ] [ 2drop ] if ;

: equate-values ( value1 value2 -- )
    ! 2dup and
    ! [
        [ escaping-values get equate ]
        [ 2array record-inner-equal-values ] 2bi
    ! ] [ 2drop ] if
    ;

: equate-all-values ( values -- )
    [ unclip-slice
      escaping-values get equate-all-with ]
    [ record-inner-equal-values ] bi
    ;

: value-escapes ( value -- )
    [ +escaping+ equate-values ]
    [ record-inner-escaping-value ] bi ;

: value-escapes? ( value -- ? )
    escaping-values get +escaping+ swap equiv? ;
