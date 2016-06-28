! Copyright (C) 2015 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors combinators.smart io.backend
io.directories.search io.files kernel namespaces sequences sets
splitting vocabs.files vocabs.hierarchy vocabs.loader
vocabs.metadata ;
IN: modern.paths

: vocabs-from ( root -- vocabs )
    "" disk-vocabs-in-root/prefix
    no-prefixes [ name>> ] map ;

: core-vocabs ( -- seq ) "resource:core" vocabs-from ;
: less-core-test-vocabs ( seq -- seq' )
    {
        "vocabs.loader.test.a"
        "vocabs.loader.test.b"
        "vocabs.loader.test.c"
        "vocabs.loader.test.d"
        "vocabs.loader.test.e"
        "vocabs.loader.test.f"
        "vocabs.loader.test.g"
        "vocabs.loader.test.h"
        "vocabs.loader.test.i"
        "vocabs.loader.test.j"
        "vocabs.loader.test.k"
        "vocabs.loader.test.l"
        "vocabs.loader.test.m"
        "vocabs.loader.test.n"
        "vocabs.loader.test.o"
        "vocabs.loader.test.p"
    } diff ;

: core-bootstrap-vocabs ( -- seq )
    core-vocabs less-core-test-vocabs ;

: filter-exists ( seq -- seq' ) [ exists? ] filter ;

! These paths have syntax errors on purpose...
: reject-some-paths ( seq -- seq' )
    {
        "resource:core/vocabs/loader/test/a/a.factor"
        "resource:core/vocabs/loader/test/b/b.factor"
        "resource:core/vocabs/loader/test/c/c.factor"
        ! Here down have parse errors
        "resource:core/vocabs/loader/test/d/d.factor"
        "resource:core/vocabs/loader/test/e/e.factor"
        "resource:core/vocabs/loader/test/f/f.factor"
        "resource:core/vocabs/loader/test/g/g.factor"
        "resource:core/vocabs/loader/test/h/h.factor"
        "resource:core/vocabs/loader/test/i/i.factor"
        "resource:core/vocabs/loader/test/j/j.factor"
        "resource:core/vocabs/loader/test/k/k.factor"
        "resource:core/vocabs/loader/test/l/l.factor"
        "resource:core/vocabs/loader/test/m/m.factor"
        "resource:core/vocabs/loader/test/n/n.factor"
        "resource:core/vocabs/loader/test/o/o.factor"
        "resource:core/vocabs/loader/test/p/p.factor"
    } [ normalize-path ] map diff
    ! Don't parse .modern files yet
    [ ".modern" tail? ] reject ;

: modern-source-paths ( names -- paths )
    [ vocab-source-path ] map filter-exists reject-some-paths ;
: modern-docs-paths ( names -- paths )
    [ vocab-docs-path ] map filter-exists reject-some-paths ;
: modern-tests-paths ( names -- paths )
    [ vocab-tests-path ] map filter-exists reject-some-paths ;

: all-vocabs ( -- seq )
    [
        vocab-roots get [ vocabs-from ] map concat
    ] { } append-outputs-as ;

: all-vocab-paths ( -- seq )
    [
        all-vocabs less-core-test-vocabs
        [ modern-source-paths ] [ modern-docs-paths ] [ modern-tests-paths ] tri
    ] { } append-outputs-as reject-some-paths filter-exists ;

: all-paths ( -- seq )
    vocab-roots get [ [ ".factor" tail? ] find-all-files ] map concat
    reject-some-paths ;
