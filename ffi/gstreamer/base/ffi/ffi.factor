! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.libraries alien.syntax combinators
gobject-introspection kernel system vocabs ;
in: gstreamer.base.ffi

COMPILE<
"gstreamer.ffi" require
COMPILE>

library: gstreamer.base

COMPILE<
"gstreamer.base" {
    { [ os windows? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libgstbase-0.10.so" cdecl add-library ] }
} cond
COMPILE>

gir: GstBase-0.10.gir
