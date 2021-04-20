USING: arrays disjoint-sets kernel namespaces sequences sets ;

IN: compiler.tree.propagation.escaping

FROM: namespaces => set ;

! * Tracking escaping values
! Taken from escape analysis, because we do this the moment we introduce values in copy

SYMBOL: escaping-values

SYMBOL: inner-escaping-values
: record-inner-escaping-value ( value -- )
    inner-escaping-values get [ adjoin ] [ drop ] if* ;

SYMBOL: inner-equal-values
: record-inner-equal-values ( values -- )
    inner-equal-values get [ adjoin ] [ drop ] if* ;

SYMBOL: +escaping+

: <escaping-values> ( -- disjoint-set )
    <disjoint-set> +escaping+ over add-atom ;

: init-escaping-values ( -- )
    <escaping-values> escaping-values set ;

: (introduce-escaping-value) ( values escaping-values -- )
    2dup disjoint-set-member?
    [ 2drop ] [ add-atom ] if ; inline

: introduce-escaping-value ( value -- )
    escaping-values get (introduce-escaping-value) ;

: introduce-escaping-values ( values -- )
    escaping-values get '[ _ (introduce-escaping-value) ] each ;

: equate-values ( value1 value2 -- )
    ! 2dup and
    ! [
        [ escaping-values get equate ]
        [ 2array record-inner-equal-values ] 2bi
    ! ] [ 2drop ] if
    ;

: equate-all-values ( values -- )
    [ [ unclip-slice ] dip
      escaping-values get equate-all-with ]
    [ record-inner-equal-values ] bi
    ;

: value-escapes ( value -- )
    [ +escaping+ equate-values ]
    [ record-inner-escaping-value ] bi ;

: value-escapes? ( value -- ? )
    escaping-values get +escaping+ swap equiv? ;
