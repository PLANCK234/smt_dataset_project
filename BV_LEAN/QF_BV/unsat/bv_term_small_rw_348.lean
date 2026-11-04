/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_348.smt2
License: CC BY 4.0
-/
import SMT.BitVec.Rewrite.Arithmetic
import SMT.BitVec.Rewrite.Bitwise

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec

theorem bv_term_small_rw_348 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor s (bvadd t (bvneg t))) = s := by
  intro n s t
  simp only [bvadd_bvneg, bvor_zero]

end BV.QF_BV.Unsat
