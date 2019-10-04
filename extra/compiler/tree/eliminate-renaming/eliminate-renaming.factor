USING: accessors arrays assocs classes.tuple compiler.tree
compiler.tree.combinators compiler.tree.value-infos grouping kernel locals
sequences stack-checker.branches ;

IN: compiler.tree.eliminate-renaming


! * Eliminating Renaming nodes

! This pass eliminates all #renaming nodes.  The result is that all input
! values are the same as their definer.

! Main iterator, returns a list of nodes for map-nodes to splice in.
GENERIC: eliminate-renaming* ( node -- nodes )

M: node eliminate-renaming* ( node -- nodes )
    clone [ [ resolve-value ] map ] change-in-d ;

M: no-data-in-node eliminate-renaming* clone ;

M: #phi eliminate-renaming* ( node -- nodes )
    clone [
        first2 [ [ +bottom+ = ] reject [ resolve-value ] map ] bi@ 2array
    ] change-phi-in-d  ;

! Only eliminate #shuffle nodes for now
M: #shuffle eliminate-renaming* drop f ;

! Also do the same with the value infos. This could be merged into
! eliminate-renaming*, though.
GENERIC: resolve-infos ( node -- node )
M: info-node resolve-infos
    [ [ [ resolve-value ] dip ] assoc-map ] change-info ;
M: node resolve-infos ;

: eliminate-renaming ( nodes -- nodes )
    [
        [
            eliminate-renaming*
            dup [ resolve-infos ] when
        ] map-nodes
    ] with-tree-value-infos ;


! ** Change #phi nodes to #mux nodes
! This is intended for pure data flow graph construction.  The inputs of #branch
! nodes are redirected to the respective #phi nodes.

TUPLE: #mux < #phi in-d ;

: convert-phis ( nodes -- nodes )
    [ dup #phi?
      [ dup phi-in-d>> [ empty? not ] any?
          [ tuple-slots f append #mux slots>tuple ]
          [ drop f ] if
      ] when
    ] map-nodes ;

:: each-node-pair ( nodes quot: ( ..a node node -- ..a ) -- )
    nodes 2 <clumps>
    [ first2 [ quot call ] keep
      dup #branch?
      [ children>> [ quot each-node-pair ] each ] [ drop ] if
    ] each ; inline recursive


: maybe-propagate-phi-pair ( node node -- )
    dup #mux?
    [ [ in-d>> ] dip in-d<< ]
    [ 2drop ] if ;

: phi>mux ( nodes -- nodes )
    convert-phis
    dup [ maybe-propagate-phi-pair ] each-node-pair ;
