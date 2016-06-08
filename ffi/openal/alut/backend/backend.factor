USING: namespaces system ;
in: openal.alut.backend

HOOK: load-wav-file os ( filename -- format data size frequency ) ;
