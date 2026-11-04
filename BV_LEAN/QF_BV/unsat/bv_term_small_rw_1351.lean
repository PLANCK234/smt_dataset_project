/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1351.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvlshr_bvneg (x y : BitVec n) :
    bvlshr (bvlshr x y) (bvneg y) = bvlshr x (bvor y (bvneg y)) := by
  by_cases h : y = literal n 0
  · subst y; simp [bvneg, bvor, bvlshr, literal]
  · rw [bvlshr_large _ _ (large_bvor_bvneg y h)]
    rcases large_or_bvneg_large y h with hy | hy
    · rw [bvlshr_large x y hy]; simp [bvlshr, literal]
    · exact bvlshr_large _ _ hy

theorem bv_term_small_rw_1351 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvlshr s t) (bvneg t)) = (bvlshr s (bvor t (bvneg t))) := by
  intro n s t
  simp only [bvlshr_bvlshr_bvneg]

end BV.QF_BV.Unsat
