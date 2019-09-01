USING: accessors compiler.tree.propagation.info
compiler.tree.propagation.known-words kernel kernel.private layouts math
math.intervals math.private random tools.test words ;
IN: compiler.tree.propagation.known-words.tests

{
    fixnum T{ interval { from { -19 t } } { to { 19 t } } }
} [
    fixnum fixnum full-interval 0 20 [a,b] mod-merge-classes/intervals
] unit-test

{
    object T{ interval { from { -20 f } } { to { 20 f } } }
} [
    object object full-interval 0 20 [a,b] mod-merge-classes/intervals
] unit-test

{ fixnum } [
    bignum <class-info>
    fixnum fixnum-interval <class/interval-info>
    \ mod "outputs" word-prop call( x y -- z )
    class>>
] unit-test

! Since 10 >bignum 5 >bignum bignum-mod => fixnum, the output class
! must be integer.
{ integer } [
    bignum <class-info> dup \ bignum-mod "outputs" word-prop call class>>
] unit-test

{ t } [
    100 random 2^ >bignum
    [ { bignum } declare 10 /mod ] call nip fixnum?
] unit-test


! Test interval info folding

! These cases cannot be folded
${ object-info } [
    -1 5 [a,b] <interval-info> 0 [a,inf] <literal-info>
    maybe-fold-interval-contains?
] unit-test

${ object-info } [
    -1 5 [a,b] <interval-info>  object-info
    maybe-fold-interval-contains?
] unit-test

${ object-info } [
    object-info -1 5 [a,b] <literal-info>
    maybe-fold-interval-contains?
] unit-test

! These cases can never be contained
${ f <literal-info> } [
    -1 <literal-info> 0 [a,inf] <literal-info>
    maybe-fold-interval-contains?
] unit-test

${ f <literal-info> } [
    -4 -1 [a,b] <interval-info> 0 [a,inf] <literal-info>
    maybe-fold-interval-contains?
] unit-test


! These are definitely contained
${ t <literal-info> } [
    1 <literal-info> 0 [a,inf] <literal-info>
    maybe-fold-interval-contains?
] unit-test

${ t <literal-info> } [
    0 256 [a,b] <interval-info> 0 [a,inf] <literal-info>
    maybe-fold-interval-contains?
] unit-test
