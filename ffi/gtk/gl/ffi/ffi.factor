! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.libraries alien.syntax combinators
gobject-introspection kernel system vocabs ;
in: gtk.gl.ffi

COMPILE<
"gtk.ffi" require
"gdk.gl.ffi" require
COMPILE>

library: gtk.gl

COMPILE<
"gtk.gl" {
    { [ os windows? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libgtkglext-x11-1.0.so" cdecl add-library ] }
} cond
COMPILE>

gir: vocab:gtk/gl/GtkGLExt-1.0.gir
