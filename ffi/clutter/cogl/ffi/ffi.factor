! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.libraries alien.syntax combinators
gobject-introspection kernel opengl.gl system vocabs ;
IN: clutter.cogl.ffi

COMPILE<
"gobject.ffi" require
COMPILE>

LIBRARY: clutter.cogl

COMPILE<
"clutter.cogl" {
    { [ os windows? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libclutter-glx-1.0.so" cdecl add-library ] }
} cond
COMPILE>

FOREIGN-ATOMIC-TYPE: GL.uint GLuint
FOREIGN-ATOMIC-TYPE: GL.enum GLenum

GIR: Cogl-1.0.gir
