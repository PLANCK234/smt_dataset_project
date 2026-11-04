/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_703.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Quotient

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvshl_bvshl_bvnot_zero (x y : BitVec n) :
    bvshl x (bvshl (bvnot (literal n 0)) y) =
      bvlshr x (bvshl (bvnot (literal n 0)) y) := by
  by_cases hy : n ≤ y.toNat
  · rw [bvshl_large _ _ hy, bvshl_zero, bvlshr_zero]
  · have hn := width_le_toNat_bvshl_bvnot_zero y (Nat.lt_of_not_ge hy)
    rw [bvshl_large _ _ hn, bvlshr_large _ _ hn]

theorem bv_term_small_rw_703 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvshl (bvnot (literal n 0)) t)) = (bvlshr s (bvshl (bvnot (literal n 0)) t)) := by
  intro n s t
  exact bvshl_bvshl_bvnot_zero s t

end BV.QF_BV.Unsat
