! Copyright (C) 2010 Anton Gorenko.
! See http://factorcode.org/license.txt for BSD license.
USING: alien alien.syntax alien.libraries combinators kernel
system
gobject-introspection glib.ffi gstreamer.ffi gstreamer.sdp.ffi ;
in: gstreamer.rtsp.ffi

<<
"gstreamer.rtsp" {
    { [ os winnt? ] [ drop ] }
    { [ os macosx? ] [ drop ] }
    { [ os unix? ] [ "libgstrtsp-0.10.so" cdecl add-library ] }
} cond
>>

! git error (there is _GstRTSPTransport only in .gir)
c-type: GstRTSPTransport

gir: vocab:gstreamer/rtsp/GstRtsp-0.10.gir

