USING: cc.defined ;

IN: cc.simple

! * Simple Encodings

CCN: omega [I]z.[I,z]f.[I,z,f]x.f@(z@z@f)@x ;
CCN: Y [I :: z -> omega]f.[I,z,f]x.f@(z@z@f)@x ;

! Functional Pearl, Scott encodings

CCN: Nil [I]x.[I,x]g.x ;
CCN: Cons  [I]x.[I,x]xs.[I,x,xs]f.[I,x,xs,f]g.(g x xs) ;
CCN: Head  [I]xs.(xs undef [I]x.[I,x]xs.x) ;
CCN: Tail  [I]xs.(xs undef [I]x.[I,x]xs.xs) ;

CCN: True  [I]a.[I,a]b.a ;
CCN: False  [I]a.[I,a]b.b ;
CCN: Ifte  [I]t.t ;
! Why not this?
CCN: IfteS [I]c.[I,c]th.[I,c,th]el.(c th el) ;

CCN: Zero  [I]f.[I,f]g.f ;
CCN: Suc  [I]n.[I,n]f.[I,n,f]g.(g n) ;
CCN: Pred  [I]n.(n undef [I]m.m) ;
CCN: One  Suc Zero ;
CCN: Zerop [I]x.( x True [I]n.False ) ;

! NOTE: The Direct recursive functions do not preserve normal forms (Infinite reduction when fed bullshit)
! Test: Add_rec foo Zero One
! CCN: Add_rec [I]n.[I,n]m.( n m [I,m]n.(Suc (Add_rec n m) ) ) ;
CCN: Add_  [I]add.[I,add]n.[I,add,n]m.(n m [I,add,m]n.(Suc (add add n m))) ;
! Seems to work
CCN: Add2  Add_ Add_ ;
! Also seems to work
CCN: Add Y ([I]add.[I,add]n.[I,add,n]m.(n m [I,add,m]n.(Suc (add n m)))) ;

! CCN: Length_rec [I]x.(x Zero ([I]x.[I,x]xs.(Suc (Length_rec xs)))) ;
CCN: Length Y [I]Ly.[I,Ly]x.(x Zero ([I,Ly]x.[I,Ly,x]xs.(Suc (Ly xs)))) ;

! Right fold
CCN: FoldList Y [I]Fl.[I,Fl]f.[I,Fl,f]def.[I,Fl,f,def]xs.( xs def ([I,Fl,f,def]h.[I,Fl,f,def,h]tl.(f h (Fl f def tl )))) ;
CCN: SumFold [I]xs.(FoldList Add Zero xs) ;

CCN: Swapply [I]x.[I,x]y.(y x) ;

! Mapping stacks to stacks
! This only makes sense in a list context?
! Dup (Cons x y) = (Cons x (Cons x y))
! Dup Nil = undef
CCN: Dup [I]x.(x undef [I]x.[I,x]xs.(Cons x (Cons x xs))) ;
! CCN: Drop [I]x.(x undef [I]x.[I,x]xs.(Cons x (Cons x xs) ) ) ;
! CCN: Dup [I]k.[I,k]f.(k f)

CCN: Eval [I]xs.(FoldList Swapply I xs) ;
CCN: K [I]x.[I,x]y.x ;

CCN: Exec [I]l.((I :: tos -> (Head l) :: rest -> (Tail l))(
                    (I :: sos -> (Head rest) :: cont -> (Tail rest))(
                        (Cons (tos sos) cont) ) ) ) ;
