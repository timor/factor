! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.libraries alien.syntax combinators
gobject-introspection kernel system vocabs ;
in: gstreamer.controller.ffi

<<
"gstreamer.ffi" require
>>

library: gstreamer.controller

<<
"gstreamer.controller" {
    { [ os windows? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libgstcontroller-0.10.so" cdecl add-library ] }
} cond
>>

gir: GstController-0.10.gir
