! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.libraries alien.syntax combinators
gobject-introspection kernel system vocabs ;
in: gstreamer.net.ffi

COMPILE<
"gstreamer.ffi" require
COMPILE>

library: gstreamer.net

COMPILE<
"gstreamer.net" {
    { [ os windows? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libgstnet-0.10.so" cdecl add-library ] }
} cond
COMPILE>

gir: GstNet-0.10.gir
