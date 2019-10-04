USING: accessors assocs compiler.tree compiler.tree.combinators
compiler.tree.def-use kernel locals namespaces sequences sequences.zipped ;
IN: compiler.tree.value-infos

! * Collecting Value Information

! Since this is intended to be used for debugging frontend passes, we cannot
! rely on pass-dependent information like value-info or def-use.  Thus, we
! iterate over all nodes and collect which node is it defined on, as well as any
! value information on it.

! These nodes have infos on in-d
UNION: info-node #call #call-recursive #return #enter-recursive
    #return-recursive ;

! These nodes don't define new values
UNION: non-def-node #return #recursive #branch #terminate #declare #alien-callback ;

! These nodes don't have any input values on in-d>>
UNION: no-data-in-node #alien-callback #declare #introduce #push #phi ;

TUPLE: tree-value-info definer info ;
: <tree-value-info> ( definer -- obj )
    tree-value-info new swap >>definer ;

SYMBOL: tree-value-infos

! ** Value Definitions

<PRIVATE
: get-tree-value-info-create ( value -- obj )
    tree-value-infos get [ drop tree-value-info new ] cache ;
PRIVATE>

: record-outputs ( node values -- )
    [ get-tree-value-info-create definer<< ] with each ;

: record-definitions ( node -- )
    dup node-defs-values record-outputs ;

! ** Value Information on Inputs

GENERIC: add-value-infos ( node -- )
M: node add-value-infos drop ;
M: info-node add-value-infos
    info>> [ swap get-tree-value-info-create info<< ] assoc-each ;

! ** Operating on Tree Nodes
! Main iterator
: collect-value-infos ( node -- )
    [ record-definitions ] [ add-value-infos ] bi ;

! ** Looking up Info by Value

: tree-value>info ( value -- tree-value-info )
    tree-value-infos get at ;

: value-definer ( value -- node/? )
    tree-value>info dup [ definer>> ] when ;

! ** Resolving actual Definitions

DEFER: resolve-value
GENERIC: resolve-value* ( value node -- value )
M: #renaming resolve-value*
    inputs/outputs swap <zipped> at
    resolve-value ;

M: object resolve-value* drop ;

: resolve-value ( value -- value )
    dup tree-value>info definer>> resolve-value* ;
    ! dup value-definer resolve-value* ;

! * Interface

! Compute infos of nodes and call quot with that
:: with-tree-value-infos ( nodes quot: ( nodes -- ... ) -- ... )
    H{ } clone tree-value-infos [
        nodes
        [ [ collect-value-infos ] each-node ]
        quot bi
    ] with-variable ; inline

! Retrieve tree-value-infos for values on node inputs
GENERIC: input-value-infos ( nodes -- values tree-value-infos )

M: node input-value-infos
    in-d>> dup [ tree-value>info ] map ;

M: #renaming input-value-infos
    inputs/outputs drop dup [ tree-value>info ] map ;
