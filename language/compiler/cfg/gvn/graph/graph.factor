! Copyright (C) 2008, 2010 Slava Pestov, 2011 Alex Vondrak.
! See http://factorcode.org/license.txt for BSD license.
USING: accessors kernel math namespaces assocs ;
in: compiler.cfg.gvn.graph

symbol: input-expr-counter

! assoc mapping vregs to value numbers
! this is the identity on canonical representatives
symbol: vregs>vns

! assoc mapping expressions to value numbers
symbol: exprs>vns

! assoc mapping value numbers to instructions
symbol: vns>insns

! assoc mapping each value number to a sequence of vregs
! sharing that value number (i.e., the congruence class)
symbol: vns>vregs

! boolean to track whether vregs>vns changes
symbol: changed?

! boolean to track when it's safe to alter the CFG in a rewrite
! method (i.e., after vregs>vns stops changing)
symbol: final-iteration?

: vn>insn ( vn -- insn ) vns>insns get at ;

: vreg>vn ( vreg -- vn ) vregs>vns get at ;

: set-vn ( vn vreg -- )
    vregs>vns get maybe-set-at [ changed? on ] when ;

: vreg>insn ( vreg -- insn ) vreg>vn vn>insn ;

: congruence-class ( vreg -- vregs )
    vreg>vn vns>vregs get at ;

: clear-exprs ( -- )
    exprs>vns get clear-assoc
    vns>insns get clear-assoc ;

: compute-congruence-classes ( -- )
    vregs>vns get H{ } clone [
        [ push-at ] curry assoc-each
    ] keep vns>vregs set ;

: init-value-graph ( -- )
    0 input-expr-counter set
    H{ } clone vregs>vns set
    H{ } clone exprs>vns set
    H{ } clone vns>insns set ;
