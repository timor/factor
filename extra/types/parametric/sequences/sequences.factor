USING: accessors arrays classes classes.algebra.private kernel sequences
types.parametric ;

IN: types.parametric.sequences

! NOTE: Assumed invariant.  Also, predicate could be extremely expensive to evaluate!
TUPLE: homogeneous-sequence-type < anonymous-predicate element-type ;

: <sequence-type> ( sequence-type element-type -- type )
    [ element-type>> [ instance? ] curry all? ] swap
    homogeneous-sequence-type boa ;
