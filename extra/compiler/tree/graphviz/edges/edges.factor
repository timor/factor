USING: accessors compiler.tree compiler.tree.eliminate-renaming
compiler.tree.graphviz.records compiler.tree.graphviz.variables
compiler.tree.propagation.info.present compiler.tree.value-infos graphviz
graphviz.notation grouping kernel locals namespaces sequences ;

IN: compiler.tree.graphviz.edges

FROM: compiler.tree => node node? ;

! Helper: Actual edge creator
: make-edge ( node next color -- edge )
    [ [ record-id ] bi@ <edge> ] dip =color ;

! * Adding Data Edges

! Implements record node protocol
M: node input-port-source ( node id -- node id )
    nip [ value-definer ] keep ;


: value-label ( value -- str )
    hide-value-labels get
    [ drop "" ]
    [ tree-value>info info>> value-info-label ] if ;

M: node input-edge-label
    nip value-label ;

GENERIC: add-input-edges ( graph node -- graph )

M: node add-input-edges
    input-edges [ add ] each ;
M: #if add-input-edges
    show-muxes get [ drop ] [ call-next-method ] if ;

<PRIVATE
: perpendicular ( -- port-dir )
    horizontal-layout get "n" "w" ? ;
PRIVATE>

M: #mux add-input-edges
    input-edges
    [ unclip-last
      [ [ add ] each ]
      [ perpendicular =headport add ] bi*
    ] unless-empty ;

! * Adding Control Edges

! Called on successive pairs on nodes.
! Since we don't have multi-methods, we overlay two generics:
! - ~add-edge-to~, which dispatches on the second node of a pair
! - ~add-edge-from~, which dispatches on the first pair of a node

GENERIC: add-edge-to ( graph prev this -- graph )
GENERIC#: add-edge-from 1 ( graph this next -- graph )
! Interface
: add-edges-between ( graph nodes -- graph )
    2 clump [
        first2
        [ add-edge-to ]
        [ add-edge-from ] 2bi
    ] each ;

: make-control-edge ( node next color -- edge )
    make-edge "dashed" =style
    "title:s" =tailport
    "title:n" =headport
    ;

: (add-color-edge) ( graph node next color -- graph )
    make-control-edge add ;

! SYMBOL: last-recursive-return

M: node add-edge-to "blue" (add-color-edge) ;
M: node add-edge-from 2drop ;

    ! make-control-edge add ;
    ! [ [ [ class-of ] bi@ ] dip "%s -> %s: %s\n" printf ] 3keep
    ! { { [ pick #recursive? ]
    !     [ drop "orange" make-control-edge
    !       "e" =tailport add ] }
    !   { [ pick #branch? ]  [ 3drop ] }
    !   [ (add-color-edge) ]
    ! } cond
    ! ;


! Phi edges are not really control edges
! TODO remove
! M: #phi add-edge-to call-next-method ;
! M: #phi add-edge-to 2drop ;
! M: #phi add-edge-to
!     drop [ add-branch-exits ] 2keep
!     "gray" make-control-edge
!     add
!     ;

! M:: #if add-edge-to ( graph node this -- graph )
!     graph node this call-next-method
!     this
!     dup children>> first2
!     [let :> ( node children1 children2 )
!      children1 [ first node swap "green" (add-color-edge) ] unless-empty
!      children2 [ first node swap "red" (add-color-edge) ] unless-empty
!      children1 add-edges-to
!      children2 add-edges-to
!     ]
!     ;

M: #terminate add-edge-from 2drop ;

M: #branch add-edge-to
    [ call-next-method ] keep
    children>> [ add-edges-between ] each ;

: branch-colors ( -- seq ) { "red" "green" "yellow" } <circular> ;

! : add-edge-unless-terminate ( graph prev next color -- graph )
!     pick #terminate?
!     (add-color-edge) ;

! called on #if-#phi pair
M: #if add-edge-from
    over children>>
    [| child branch phi i |
     i branch-colors nth :> col
     child empty?
     [ branch phi col (add-color-edge) ]
     [
         branch child first col (add-color-edge)
         child ends-with-terminate? [ child last phi col (add-color-edge) ] unless
     ] if
    ] 2with each-index ;
    ! [let :> ( node children1 children2 )
    !  children1 [ first node swap "green" (add-color-edge) ] unless-empty
    !  children2 [ first node swap "red" (add-color-edge) ] unless-empty
    !  children1 add-edges-between
    !  children2 add-edges-between
    ! ]

M: #phi add-edge-to
    "gray" make-edge
    "w" =tailport
    "w" =headport
    add ;

SYMBOL: recursive-stack
recursive-stack [ V{ } clone ] initialize

M: #recursive add-edge-from
    "orange" make-control-edge
    "e" =tailport add
    ;

M: #recursive add-edge-to
    [ call-next-method ] keep
    dup recursive-stack get push
    dup child>>
    [
        ! [
            first "purple" (add-color-edge)
    ! ]
        ! [ last swap "orange"
        !   make-control-edge
        !   "w" =tailport
        !   "w" =headport
        !   add
        ! ] 2bi
    ]
    [ add-edges-between ] bi
    recursive-stack get pop drop ;

M: #call-recursive add-edge-to
    nip
    recursive-stack get last child>> first
    "purple" make-control-edge
    "w" =tailport
    "w" =headport add ;

M: #return-recursive add-edge-to
    [ call-next-method ] keep
    recursive-stack get last "orange" make-control-edge
    "w" =tailport
    "w" =headport add ;

! : add-branch-exits ( graph node next -- graph )
!     swap children>> [ ?last
!                       [ swap "blue" (add-color-edge) ]
!                       [ drop ] if*
!     ] with each ;

! Interface
! : add-edges-to ( graph nodes -- graph )
!     [ #phi? ] reject
!     2 clump [
!         first2
!         [ over #branch? [ add-branch-exits ] [ 2drop ] if ]
!         [ "blue" add-edge-to ] 2bi
!     ] each ;

! * Adding Phi Edges

! DEFER: add-phi-edges

! ! Called on successive pairs on nodes.
! ! Dispatches on the first node of the pair.
! GENERIC#: add-phi-edge 1 ( graph node next -- graph )
! M: node add-phi-edge 2drop ;
! M: #branch add-phi-edge
!     [
!         "gray" make-edge
!         "title:w" =tailport
!         "title:w" =headport
!         add
!     ] keepd
!     children>> [ add-phi-edges ] each ;

! M: #recursive add-phi-edge drop child>> add-phi-edges ;

! Interface
! : add-phi-edges ( graph nodes -- graph )
!     2 clump [
!         first2 add-phi-edge
!     ] each ;
