USING: accessors arrays assocs euler.b-rep
game.models.half-edge kernel locals math math.vectors
math.vectors.simd.cords sequences sets typed fry ;
FROM: sequences.private => nth-unsafe set-nth-unsafe ;
IN: euler.b-rep.subdivision

: <vertex> ( position -- vertex ) vertex new swap >>position ; inline

: face-points ( faces -- face-pts )
    [ edge>> face-midpoint <vertex> ] map ; inline

:: edge-points ( edges edge-indices face-indices face-points -- edge-pts )
    edges length 0 <array> set: edge-pts

    edges |[ edge n |
        edge opposite-edge>> set: opposite-edge
        opposite-edge edge-indices at set: opposite-n

        n opposite-n < [
            edge          vertex>> position>>
            opposite-edge vertex>> position>> v+
            edge          face>> face-indices at face-points nth position>> v+
            opposite-edge face>> face-indices at face-points nth position>> v+
            0.25 v*n
            <vertex>
            [ n edge-pts set-nth-unsafe ]
            [ opposite-n edge-pts set-nth-unsafe ] bi
        ] when
    ] each-index

    edge-pts ; inline

:: vertex-points ( vertices edge-indices face-indices edge-pts face-points -- vertex-pts )
    vertices |[ vertex |
        0 double-4{ 0 0 0 0 } double-4{ 0 0 0 0 }
        vertex edge>> |[ valence face-sum edge-sum edge |
            valence 1 +
            face-sum edge face>> face-indices at face-points nth position>> v+
            edge-sum edge next-edge>> vertex>> position>> v+
        ] each-vertex-edge set: ( valence face-sum edge-sum )
        valence >float set: fvalence
        face-sum fvalence v/n set: face-avg
        edge-sum fvalence v/n set: edge-avg
        face-avg  edge-avg v+  vertex position>> fvalence 2.0 - v*n v+
        fvalence v/n
        <vertex>
    ] map ; inline

TYPED:: subdivide ( brep: b-rep -- brep': b-rep )
    brep vertices>> set: vertices
    brep edges>>    set: edges
    brep faces>>    set: faces

    vertices >index-hash set: vertex-indices
    edges    >index-hash set: edge-indices
    faces    >index-hash set: face-indices

    faces face-points set: face-pts
    edges edge-indices face-indices face-pts edge-points set: edge-pts
    vertices edge-indices face-indices edge-pts face-pts vertex-points set: vertex-pts

    V{ } clone set: sub-edges
    V{ } clone set: sub-faces

    vertices [
        edge>> |[ edg |
            edg edge-indices at edge-pts nth set: point-a
            edg next-edge>> set: next-edg
            next-edg vertex>> set: next-vertex
            next-vertex vertex-indices at vertex-pts nth set: point-b
            next-edg edge-indices at edge-pts nth set: point-c
            edg face>> face-indices at face-pts nth set: point-d

            face new
                dup >>base-face set: fac

            b-edge new
                fac >>face
                point-a >>vertex set: edg-a
            b-edge new
                fac >>face
                point-b >>vertex set: edg-b
            b-edge new
                fac >>face
                point-c >>vertex set: edg-c
            b-edge new
                fac >>face
                point-d >>vertex set: edg-d
            edg-a fac   edge<<
            edg-b edg-a next-edge<<
            edg-c edg-b next-edge<<
            edg-d edg-c next-edge<<
            edg-a edg-d next-edge<<

            fac sub-faces push
            edg-a sub-edges push
            edg-b sub-edges push
            edg-c sub-edges push
            edg-d sub-edges push

            point-a [ edg-a or ] change-edge drop
            point-b [ edg-b or ] change-edge drop
            point-c [ edg-c or ] change-edge drop
            point-d [ edg-d or ] change-edge drop
        ] each-vertex-edge
    ] each

    b-rep new
        sub-faces { } like >>faces
        sub-edges { } like >>edges
        face-pts edge-pts vertex-pts 3append members { } like >>vertices
    [ connect-opposite-edges ] keep ;
