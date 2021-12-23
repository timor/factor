USING: fmc fmc.printing kernel math.private tools.test types.util ;
IN: fmc.tests

: add ( a b -- c ) fixnum+ ;

: rec ( x -- x ) rec ;

[ [ rec ] >fmc ] must-fail

{ "λ⟨x1⟩·λ⟨y1⟩·[x1]λ·[y1]λ·λ⟨a1⟩·λ⟨b1⟩·[b1]λ·[a1]λ·fixnum+·✴" }
[ [ [ swap add ] >fmc pprint-fmc ] with-var-names ] unit-test
