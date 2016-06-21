! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.libraries alien.syntax combinators
gobject-introspection kernel system vocabs ;
IN: clutter.gtk.ffi

COMPILE<
"clutter.ffi" require
"gtk.ffi" require
COMPILE>

LIBRARY: clutter.gtk

COMPILE<
"clutter.gtk" {
    { [ os windows? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libclutter-gtk-1.0.so" cdecl add-library ] }
} cond
COMPILE>

gir: GtkClutter-1.0.gir
