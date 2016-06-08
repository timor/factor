USING: compiler.cfg.instructions
compiler.cfg.representations.selection tools.test ;
in: compiler.cfg.representations.selection.tests

{ t t f } [
    T{ ##load-integer } peephole-optimizable?
    T{ ##shr-imm } peephole-optimizable?
    T{ ##call } peephole-optimizable?
] unit-test
