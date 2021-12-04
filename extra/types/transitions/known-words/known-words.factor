USING: classes.algebra kernel kernel.private types.transitions ;

IN: types.transitions.known-words


M: \ ? parallel-defs drop
    {
        [ drop { not{ POSTPONE: f } ?? } declare nip ]
        [ nip { POSTPONE: f ?? } declare nip ]
    } ;

! M: \ both-fixnums? parallel-defs drop
!     {
!         [ { fixnum fixnum } declare 2drop t ]
!         [ {  } ]
!     }
