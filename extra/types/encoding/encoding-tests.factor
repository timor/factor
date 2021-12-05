USING: tools.test types.encoding ;
IN: types.encoding.tests

{ fixnum array }
[ { fixnum array } <type-list> 0 over type-nth 1 pick type-nth nipd ] unit-test
