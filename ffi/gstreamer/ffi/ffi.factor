! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.c-types alien.libraries alien.syntax combinators
gobject-introspection kernel system vocabs ;
IN: gstreamer.ffi

COMPILE<
"glib.ffi" require
"gobject.ffi" require
"gmodule.ffi" require
COMPILE>

LIBRARY: gstreamer

COMPILE<
"gstreamer" {
    { [ os windows? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libgstreamer-0.10.so" cdecl add-library ] }
} cond
COMPILE>

PRIVATE<

! types from libxml2

TYPEDEF: void* xmlNodePtr
TYPEDEF: void* xmlDocPtr
TYPEDEF: void* xmlNsPtr

FOREIGN-ATOMIC-TYPE: libxml2.NodePtr xmlNodePtr
FOREIGN-ATOMIC-TYPE: libxml2.DocPtr xmlDocPtr
FOREIGN-ATOMIC-TYPE: libxml2.NsPtr xmlNsPtr

PRIVATE>

GIR: Gst-0.10.gir
