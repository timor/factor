! Copyright (C) 2010 Erik Charlebois.
! See http://factorcode.org/license.txt for BSD license.
USING: locals io.encodings.ascii io.encodings.string sequences
math specialized-arrays alien.c-types math.order alien opencl tools.test
accessors arrays destructors kernel namespaces alien.data ;
FROM: alien.c-types => float ;
SPECIALIZED-ARRAY: float
IN: opencl.tests

CONSTANT: kernel-source [[
__kernel void square(
    __global float* input,
    __global float* output,
    const unsigned int count)
{
    int i = get_global_id(0);
    if (i < count)
        output[i] = input[i] * input[i];
}
]]

:: opencl-square ( in -- out )
    [
        in byte-length                         set: num-bytes
        in length                              set: num-floats
        cl-platforms first devices>> first     set: device
        device 1array <cl-context> &dispose    set: context
        context device f f <cl-queue> &dispose set: queue

        context device queue [
            "" kernel-source 1array <cl-program> &dispose "square" <cl-kernel> &dispose set: kernel
            cl-read-access num-bytes in <cl-buffer> &dispose set: in-buffer
            cl-write-access num-bytes f <cl-buffer> &dispose set: out-buffer

            kernel in-buffer out-buffer num-floats uint <ref> 3array
            { num-floats } [ ] cl-queue-kernel &dispose drop

            cl-finish

            out-buffer 0 num-bytes <cl-buffer-range>
            cl-read-buffer num-floats \ float <c-direct-array>
        ] with-cl-state
    ] with-destructors ;

{ float-array{ 1.0 4.0 9.0 16.0 100.0 } }
[ float-array{ 1.0 2.0 3.0 4.0 10.0 } opencl-square ] unit-test
