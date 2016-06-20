! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.libraries alien.syntax combinators
gobject-introspection kernel system vocabs vocabs.loader ;
IN: gdk.gl.ffi

COMPILE<
"gdk.ffi" require
COMPILE>

library: gdk.gl

COMPILE<
"gdk.gl" {
    { [ os windows? ] [ "libgdkglext-win32-1.0-0.dll" cdecl add-library ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libgdkglext-x11-1.0.so" cdecl add-library ] }
} cond
COMPILE>

gir: vocab:gdk/gl/GdkGLExt-1.0.gir
