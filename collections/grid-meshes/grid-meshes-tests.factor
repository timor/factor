in: grid-meshes.tests
USING: alien.c-types alien.data grid-meshes grid-meshes.private
specialized-arrays tools.test ;
specialized-array: float

{
    float-array{
        0.0 0.0 0.0 1.0
        0.0 0.0 0.5 1.0
        0.5 0.0 0.0 1.0
        0.5 0.0 0.5 1.0
        1.0 0.0 0.0 1.0
        1.0 0.0 0.5 1.0
        0.0 0.0 0.5 1.0
        0.0 0.0 1.0 1.0
        0.5 0.0 0.5 1.0
        0.5 0.0 1.0 1.0
        1.0 0.0 0.5 1.0
        1.0 0.0 1.0 1.0
    }
} [ { 2 2 } vertex-array float cast-array ] unit-test
