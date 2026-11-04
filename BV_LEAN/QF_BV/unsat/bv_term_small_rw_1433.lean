/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1433.smt2
License: CC BY 4.0
-/
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec

theorem bv_term_small_rw_1433 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand (bvand s (bvnot t)) t) = (literal n 0) := by
  intro n s t
  rw [bvand_assoc, bvand_comm (bvnot t) t,
    bvand_bvnot, bvand_zero]

end BV.QF_BV.Unsat
