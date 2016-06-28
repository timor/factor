USING: classes.struct classes.tuple functors tools.test math
words kernel parser io.streams.string generic ;
QUALIFIED-WITH: alien.c-types c ;
IN: functors.tests

COMPILE<

FUNCTOR< define-box ( T -- )

B DEFINES-CLASS ${T}-box
<B> DEFINES <${B}>

WHERE

TUPLE: B { value T } ;

C: <B> B ;

FUNCTOR>

\ float define-box

COMPILE>

{ 1 0 } [ define-box ] must-infer-as

[ T{ float-box f 5.0 } ] [ 5.0 <float-box> ] unit-test

: twice ( word -- )
    [ execute ] [ execute ] bi ; inline
COMPILE<

FUNCTOR< wrapper-test ( W -- )

WW DEFINES ${W}${W}

WHERE

: WW ( a -- b ) \ W twice ;

FUNCTOR>

\ sq wrapper-test

COMPILE>

[ 16 ] [ 2 sqsq ] unit-test

COMPILE<

FUNCTOR< wrapper-test-2 ( W -- )

W DEFINES ${W}

WHERE

: W ( a b -- c ) \ + execute ;

FUNCTOR>

"blah" wrapper-test-2

COMPILE>

[ 4 ] [ 1 3 blah ] unit-test

COMPILE<

FUNCTOR< symbol-test ( W -- )

W DEFINES ${W}

WHERE

SYMBOL: W

FUNCTOR>

"blorgh" symbol-test

COMPILE>

[ blorgh ] [ blorgh ] unit-test

COMPILE<

FUNCTOR< generic-test ( W -- )

W DEFINES ${W}

WHERE

GENERIC: W ( a -- b ) ;
M: object W ;
M: integer W 1 + ;

FUNCTOR>

"snurv" generic-test

COMPILE>

[ 2   ] [ 1   snurv ] unit-test
[ 3.0 ] [ 3.0 snurv ] unit-test

! Does replacing an ordinary word with a functor-generated one work?
[ [ ] ] [
    "IN: functors.tests

    TUPLE: some-tuple ;
    : some-word ( -- ) ;
    GENERIC: some-generic ( a -- b ) ;
    M: some-tuple some-generic ;
    SYMBOL: some-symbol" <string-reader> "functors-test" parse-stream
] unit-test

: test-redefinition ( -- )
    [ t ] [ "some-word" "functors.tests" lookup-word >boolean ] unit-test
    [ t ] [ "some-tuple" "functors.tests" lookup-word >boolean ] unit-test
    [ t ] [ "some-generic" "functors.tests" lookup-word >boolean ] unit-test
    [ t ] [
        "some-tuple" "functors.tests" lookup-word
        "some-generic" "functors.tests" lookup-word lookup-method >boolean
    ] unit-test ;
    [ t ] [ "some-symbol" "functors.tests" lookup-word >boolean ] unit-test

test-redefinition

FUNCTOR< redefine-test ( W -- )

W-word DEFINES ${W}-word
W-tuple DEFINES-CLASS ${W}-tuple
W-generic DEFINES ${W}-generic
W-symbol DEFINES ${W}-symbol

WHERE

TUPLE: W-tuple ;
: W-word ( -- ) ;
GENERIC: W-generic ( a -- b ) ;
M: W-tuple W-generic ;
SYMBOL: W-symbol

FUNCTOR>

[ [ ] ] [
    "IN: functors.tests
    COMPILE< \"some\" redefine-test COMPILE>" <string-reader> "functors-test" parse-stream
] unit-test

test-redefinition

COMPILE<

FUNCTOR< define-a-struct ( T NAME TYPE N -- )

T-class DEFINES-CLASS ${T}

WHERE

STRUCT: T-class
    { NAME c:longlong }
    { x { TYPE 4 } }
    { y { c:short N } }
    { z TYPE initial: 5 }
    { float { c:float 2 } } ;

FUNCTOR>

"a-struct" "nemo" c:char 2 define-a-struct

COMPILE>

[
    {
        T{ struct-slot-spec
            { name "nemo" }
            { offset 0 }
            { class integer }
            { initial 0 }
            { type c:longlong }
        }
        T{ struct-slot-spec
            { name "x" }
            { offset 8 }
            { class object }
            { initial f }
            { type { c:char 4 } }
        }
        T{ struct-slot-spec
            { name "y" }
            { offset 12 }
            { class object }
            { initial f }
            { type { c:short 2 } }
        }
        T{ struct-slot-spec
            { name "z" }
            { offset 16 }
            { class fixnum }
            { initial 5 }
            { type c:char }
        }
        T{ struct-slot-spec
            { name "float" }
            { offset 20 }
            { class object }
            { initial f }
            { type { c:float 2 } }
        }
    }
] [ a-struct struct-slots ] unit-test

COMPILE<

FUNCTOR< define-an-inline-word ( W -- )

W DEFINES ${W}
W-W DEFINES ${W}-${W}

WHERE

: W ( -- ) ; inline
: W-W ( -- ) W W ;

FUNCTOR>

"an-inline-word" define-an-inline-word

COMPILE>

[ t ] [ \ an-inline-word inline? ] unit-test
[ f ] [ \ an-inline-word-an-inline-word inline? ] unit-test

COMPILE<

FUNCTOR< define-a-final-class ( T W -- )

T DEFINES-CLASS ${T}
W DEFINES ${W}

WHERE

TUPLE: T ; final

: W ( -- ) ;

FUNCTOR>

"a-final-tuple" "a-word" define-a-final-class

COMPILE>

[ t ] [ a-final-tuple final-class? ] unit-test
