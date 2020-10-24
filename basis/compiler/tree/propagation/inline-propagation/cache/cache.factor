USING: accessors arrays assocs compiler.messages formatting kernel locals
namespaces sequences stack-checker.dependencies ;
IN: compiler.tree.propagation.inline-propagation.cache

SINGLETONS: per-unit per-word ;
! If this is enabled, a shared inline-info-cache is set for each compilation unit
SYMBOL: inline-propagation
: inline-propagation? ( -- ? ) inline-propagation get-global ;
! inline-propagation [ t ] initialize

! An assoc storing cached inlined-infos for different value-info inputs for each word
SYMBOL: inline-info-cache

GENERIC: set-inline-propagation ( how -- )
M: t set-inline-propagation inline-propagation set-global
    inline-info-cache [ H{ } clone ] initialize ;
M: per-unit set-inline-propagation inline-propagation set-global
    f inline-info-cache set-global ;
M: per-word set-inline-propagation inline-propagation set-global
    f inline-info-cache set-global ;
M: f set-inline-propagation inline-propagation set-global
    f inline-info-cache set-global ;

! Everything run inside this shares an inline-info-cache
: with-inline-info-cache ( quot -- ) [ H{ } clone inline-info-cache ] dip with-variable ; inline

TUPLE: inline-propagation-entry { classes read-only } { dependencies read-only } ;
C: <inline-propagation-entry> inline-propagation-entry
! : cache-inline-propagation-result ( classes deps sig cache -- )
!     [ <inline-propagation-entry> ] 2dip set-at ;

! We also have to cache the dependencies collected during inlining on the
! respective words, so that if we use a cached entry, the dependencies are
! updated as well.
SYMBOL: inline-propagation-dependencies
inline-propagation-dependencies [ H{ } clone ] initialize

: get-dependencies-namespace ( -- assoc )
    { dependencies generic-dependencies conditional-dependencies } [ dup get ] H{ } map>assoc ;

: short-signature ( inline-signature -- seq )
    [ class>> ] [ slots>> ] bi
    [ [ dup [ short-signature ] when ] map swap prefix ] unless-empty ;

: invalidate-inline-info ( words -- )
    ! dup inline-propagation-dependencies get '[| name
    !     _ delete-at*
    ! ] each
    inline-info-cache get [| word cache |
                           word cache delete-at* :> ( old deleted? )
                           old assoc-size :> num-deleted
                           deleted? [ [
                                 num-deleted word old [ [ [ short-signature ] map ] [ classes>> ] bi* 2array ] { } assoc>map
                                 "Deleted %d inline-cache entries for word %u:\n%u" printf
                           ] with-trace-file-output ] when
                           deleted? num-deleted 0 ? ] curry map-sum
    "--- # of invalidated inline-info cache entries: %d" 1 format-compiler-message ;


! * Performance checking
SYMBOL: inline-info-cache-hits
SYMBOL: inline-info-cache-misses
inline-info-cache-hits [ 0 ] initialize
inline-info-cache-misses [ 0 ] initialize

: inline-info-cache-report ( -- )
    inline-info-cache-hits get inline-info-cache-misses get
    2dup [ 0 = ] both? [ 2drop ] [ "Last Inline Info Cache Stats (hits/misses): %d/%d" printf ] if
    [
        0 inline-info-cache-hits set
        0 inline-info-cache-misses set
    ] with-global ;

: trace-inline-info-cache-report ( -- )
    [ inline-info-cache-report ] with-trace-file-output ;
