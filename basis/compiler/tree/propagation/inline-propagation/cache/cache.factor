USING: accessors assocs compiler.messages fry kernel namespaces sequences
stack-checker.dependencies ;
IN: compiler.tree.propagation.inline-propagation.cache

SYMBOL: inline-propagation
: inline-propagation? ( -- ? ) inline-propagation get ;

: with-inline-propagation ( quot -- ) inline-propagation swap with-variable-on ; inline

! An assoc storing cached inlined-infos for different value-info inputs for each word
SYMBOL: inline-info-cache
inline-info-cache [ H{ } clone ] initialize

TUPLE: inline-propagation-entry { classes read-only } { dependencies read-only } ;
C: <inline-propagation-entry> inline-propagation-entry
! : cache-inline-propagation-result ( classes deps sig cache -- )
!     [ <inline-propagation-entry> ] 2dip set-at ;

! We also have to cache the dependencies collected during inlining on the
! respective words, so that if we use a cached entry, the dependencies are
! updated as well.
SYMBOL: inline-propagation-dependencies
inline-propagation-dependencies [ H{ } clone ] initialize

SYMBOL: current-inline-propagation-dependencies
: get-dependencies-namespace ( -- assoc )
    { dependencies generic-dependencies conditional-dependencies } [ dup get ] H{ } map>assoc ;


: invalidate-inline-info ( words -- )
    dup inline-propagation-dependencies get '[ _ delete-at ] each
    inline-info-cache get '[ _ delete-at* [ assoc-size ] [ drop 0 ] if ] map-sum
    "--- # of invalidated inline-info cache entries: %d" 1 format-compiler-message ;

