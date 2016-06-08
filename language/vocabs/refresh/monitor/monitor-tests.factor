USING: tools.test vocabs.refresh.monitor io.pathnames ;
in: vocabs.refresh.monitor.tests

{ "kernel" } [ "core/kernel/kernel.factor" path>vocab ] unit-test
{ "kernel" } [ "core/kernel/" path>vocab ] unit-test
{ "kernel" } [ "core/kernel/" resource-path path>vocab ] unit-test
