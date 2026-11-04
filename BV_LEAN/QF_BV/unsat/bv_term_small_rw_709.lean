/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_709.smt2
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

theorem bv_term_small_rw_709 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor s (bvshl (bvshl s s) t)) = (bvadd s (bvshl (bvshl s s) t)) := by
  intro n s t
  simp only [bvand_bvshl_bvshl_low, bvor_eq_bvadd_of_bvand_eq_zero]

end BV.QF_BV.Unsat
