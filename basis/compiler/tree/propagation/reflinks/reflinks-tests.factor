USING: accessors compiler.test compiler.tree.propagation.info
 kernel sequences tools.test ;
IN: compiler.tree.propagation.reflinks.tests

! TUPLE: circle me ;

! { t } [ [ [ circle new dup >>me me>> ] final-info ] with-rw first value-info-state? ] unit-test
