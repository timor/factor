USING: accessors combinators compiler.test compiler.tree
compiler.tree.propagation.copy compiler.tree.propagation.info
compiler.tree.propagation.nodes compiler.tree.propagation.reflinks
compiler.tree.propagation.slot-refs
generic.single kernel sequences tools.test ;
IN: compiler.tree.propagation.reflinks.tests

TUPLE: foo { a read-only initial: 42 } b ;
C: <foo> foo

: frob ( x -- ) drop ;
: poke ( x -- x ) ; flushable

{ f } [ { 1 } f \ frob <#call> non-escaping-call? ] unit-test
{ t } [ { 1 } f \ frob <#call> \ propagate-escape method-for-object
        M\ #call propagate-escape =
      ] unit-test
{ t } [ { 1 } f \ poke <#call> non-escaping-call? ] unit-test
{ t } [ { 1 } f \ frob <#call> \ propagate-escape method-for-object
        M\ #call propagate-escape =
      ] unit-test

! An inlined accessor shouldn't destroy value info
{ t t t t } [
    [
        { 1 2 3 4 } introduce-values
        foo <class-info> 1 set-value-info
        { 1 } { 2 } \ a>> <#call>
        [ propagate-around ] keep
        {
            [ inlined-call? ]
            [ \ propagate-escape method-for-object M\ non-escaping-call propagate-escape = ]
            ! Expect inlined method
            [ body>> first \ propagate-escape method-for-object M\ non-escaping-call propagate-escape = ]
            ! Expect inlined slot call
            [ body>> first body>> third \ propagate-escape method-for-object M\ non-escaping-call propagate-escape = ]
        } cleave
    ] with-values
] unit-test

! Same for literal input
{ t t t t } [
    [
        { 1 2 3 4 } introduce-values
        T{ foo f 11 22 } <literal-info> 1 set-value-info
        { 1 } { 2 } \ a>> <#call>
        [ propagate-around ] keep
        {
            [ inlined-call? ]
            [ \ propagate-escape method-for-object M\ non-escaping-call propagate-escape = ]
            ! Expect inlined method
            [ body>> first \ propagate-escape method-for-object M\ non-escaping-call propagate-escape = ]
            ! Expect inlined slot call
            [ body>> first body>> third \ propagate-escape method-for-object M\ non-escaping-call propagate-escape = ]
        } cleave
    ] with-values
] unit-test


! Invalid writes
! TODO: make sure invalid writes don't break anything !
! {  } [ [  [ foo new 42 >>a ]  propagated-tree ] with-rw ] unit-test
! {  } [ [  [ foo new 42 >>a a>> ]  propagated-tree ] with-rw ] unit-test

! Test basic links
{ 1 2 }
[ [ [ 11 22 <foo> 42 >>b [ b>> ] keep [ b>> ] keep ] final-info last slots>> third
  backref>> [ defined-by>> ] [ defines>> ] bi [ length ] bi@
  ] with-rw ] unit-test


! Link merging
{ 2 2 }
[ [ [ [ 11 22 <foo> 42 >>b ] [ 11 22 <foo> 43 >>b ] if [ b>> ] keep [ b>> ] keep ] final-info last slots>> third
    backref>> [ defined-by>> ] [ defines>> ] bi [ length ] bi@
  ] with-rw ] unit-test

{ 2 4 }
[ [ [ [ 11 22 <foo> 42 >>b [ b>> ] keep [ b>> ] keep ]
      [ 11 22 <foo> 43 >>b [ b>> ] keep [ b>> ] keep ] if  ] final-info last slots>> third
    backref>> [ defined-by>> ] [ defines>> ] bi [ length ] bi@
  ] with-rw ] unit-test
