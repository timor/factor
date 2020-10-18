USING: kernel namespaces ;
IN: compiler.tree.propagation.inline-propagation.cache

SYMBOL: inline-propagation
: inline-propagation? ( -- ? ) inline-propagation get ;

: with-inline-propagation ( quot -- ) inline-propagation swap with-variable-on ; inline

! An assoc storing cached inlined-infos for different value-info inputs for each word
SYMBOL: inline-info-cache

: with-inline-info-cache ( quot -- ) [ H{ } clone inline-info-cache ] dip with-variable ; inline
