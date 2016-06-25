! Copyright (C) 2009 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel present io math sequences assocs math.ranges
math.order fry tools.time locals smalltalk.selectors
smalltalk.ast smalltalk.classes ;
IN: smalltalk.library

selector\ print
selector\ asString

M: object selector-print dup present print ;
M: object selector-asString present ;

selector\ print:
selector\ nextPutAll:
selector\ tab
selector\ nl

M: object \ selector-print: [ present ] dip stream-print nil ;
M: object \ selector-nextPutAll: selector-print: ;
M: object selector-tab "    " swap selector-print: ;
M: object selector-nl stream-nl nil ;

selector\ +
selector\ -
selector\ *
selector\ /
selector\ <
selector\ >
selector\ <=
selector\ >=
selector\ =

M: object selector-+  swap +  ;
M: object selector--  swap -  ;
M: object selector-*  swap *  ;
M: object selector-/  swap /  ;
M: object selector-<  swap <  ;
M: object selector->  swap >  ;
M: object selector-<= swap <= ;
M: object selector->= swap >= ;
M: object selector-=  swap =  ;

selector\ min:
selector\ max:

M: object \ selector-min: min ;
M: object \ selector-max: max ;

selector\ ifTrue:
selector\ ifFalse:
selector\ ifTrue:ifFalse:

M: object \ selector-ifTrue: [ call( -- result ) ] [ drop nil ] if ;
M: object \ selector-ifFalse: [ drop nil ] [ call( -- result ) ] if ;
M: object \ selector-ifTrue:ifFalse: [ drop call( -- result ) ] [ nip call( -- result ) ] if ;

selector\ isNil

M: object selector-isNil nil eq? ;

selector\ at:
selector\ at:put:

M: sequence \ selector-at: nth ;
M: sequence \ selector-at:put: ( key value receiver -- receiver ) [ swapd set-nth ] keep ;

M: assoc \ selector-at: at ;
M: assoc \ selector-at:put: ( key value receiver -- receiver ) [ swapd set-at ] keep ;

selector\ do:

M:: object \ selector-do: ( quot receiver -- nil )
    receiver [ quot call( elt -- result ) drop ] each nil ;

selector\ to:
selector\ to:do:

M: object \ selector-to: swap [a,b] ;
M:: object \ selector-to:do: ( to quot from -- nil )
    from to [a,b] [ quot call( i -- result ) drop ] each nil ;

selector\ value
selector\ value:
selector\ value:value:
selector\ value:value:value:
selector\ value:value:value:value:

M: object selector-value call( -- result ) ;
M: object \ selector-value: call( input -- result ) ;
M: object \ selector-value:value: call( input input -- result ) ;
M: object \ selector-value:value:value: call( input input input -- result ) ;
M: object \ selector-value:value:value:value: call( input input input input -- result ) ;

selector\ new

M: object selector-new new ;

selector\ time

M: object selector-time $[ _ call( -- result ) ] time ;
