/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_635.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvshl_bvor_bvneg (x y : BitVec n) :
    bvshl x (bvor y (bvneg y)) = bvlshr x (bvor y (bvneg y)) := by
  by_cases h : y = literal n 0
  · subst y; simp [bvneg, bvor, bvshl_eq_shiftLeft, bvlshr, literal]
  · rw [bvshl_large _ _ (large_bvor_bvneg y h), bvlshr_large _ _ (large_bvor_bvneg y h)]

theorem bv_term_small_rw_635 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvor (bvneg t) t)) = (bvlshr s (bvor t (bvneg t))) := by
  intro n s t
  simp only [bvor_comm, bvshl_bvor_bvneg]

end BV.QF_BV.Unsat
