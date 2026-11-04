/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1419.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvor_right (x y : BitVec n) :
    bvlshr y (bvor x y) = literal n 0 :=
  bvlshr_eq_zero_of_le y _ SMT.Nat.right_le_or

private theorem bvshl_bvlshr_bvneg (x y : BitVec n) :
    bvshl (bvlshr x y) (bvneg y) = bvlshr x (bvor y (bvneg y)) := by
  by_cases h : y = literal n 0
  · subst y; simp [bvneg, bvor, bvshl_eq_shiftLeft, bvlshr, literal]
  · rw [bvlshr_large _ _ (large_bvor_bvneg y h)]
    rcases large_or_bvneg_large y h with hy | hy
    · rw [bvlshr_large x y hy]; simp [bvshl_eq_shiftLeft, literal]
    · exact bvshl_large _ _ hy

theorem bv_term_small_rw_1419 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvlshr s (bvneg s)) s) = (literal n 0) := by
  intro n s t
  have h := bvshl_bvlshr_bvneg s (bvneg s)
  simpa only [bvneg_bvneg, bvlshr_bvor_right] using h

end BV.QF_BV.Unsat
