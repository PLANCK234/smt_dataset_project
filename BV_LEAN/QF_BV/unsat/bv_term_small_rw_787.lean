/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_787.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvand_bvshl_bvshl_low (x y z : BitVec n) :
    bvand x (bvshl (bvshl y x) z) = literal n 0 := by
  rw [bvshl_bvshl_comm, bvand_bvshl_self]

theorem bv_term_small_rw_787 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand s (bvshl (bvshl t s) t)) = (literal n 0) := by
  intro n s t
  simp only [bvand_bvshl_bvshl_low]

end BV.QF_BV.Unsat
