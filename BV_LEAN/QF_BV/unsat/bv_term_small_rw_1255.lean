/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1255.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvor_left (x y : BitVec n) :
    bvlshr x (bvor x y) = literal n 0 :=
  bvlshr_eq_zero_of_le x _ SMT.Nat.left_le_or

private theorem bvshl_bvshl_bvneg (x y : BitVec n) :
    bvshl (bvshl x y) (bvneg y) = bvlshr x (bvor y (bvneg y)) := by
  by_cases h : y = literal n 0
  · subst y; simp [bvneg, bvor, bvshl_eq_shiftLeft, bvlshr, literal]
  · rw [bvlshr_large _ _ (large_bvor_bvneg y h)]
    rcases large_or_bvneg_large y h with hy | hy
    · rw [bvshl_large x y hy]; simp [bvshl_eq_shiftLeft, literal]
    · exact bvshl_large _ _ hy

theorem bv_term_small_rw_1255 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvshl s s) (bvneg s)) = (literal n 0) := by
  intro n s t
  simp only [bvshl_bvshl_bvneg, bvlshr_bvor_left]

end BV.QF_BV.Unsat
