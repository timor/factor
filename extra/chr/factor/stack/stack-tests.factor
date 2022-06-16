USING: kernel ;
IN: chr.factor.stack.tests


! must be the same:
! [ bi@ ] and it's inlined expansion

: mybiat ( -- code )
    [ dup [ dip ] dip call ] ;

: mybiatex ( -- code )
    [ [ 1 + ] ] mybiat compose ;
