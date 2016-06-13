! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.libraries alien.syntax combinators
gobject-introspection kernel system vocabs ;
in: gstreamer.controller.ffi

COMPILE<
"gstreamer.ffi" require
COMPILE>

library: gstreamer.controller

COMPILE<
"gstreamer.controller" {
    { [ os windows? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libgstcontroller-0.10.so" cdecl add-library ] }
} cond
COMPILE>

gir: GstController-0.10.gir
