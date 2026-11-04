/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1256.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvshl_bvshl_bvnot (x y : BitVec n) :
    bvshl (bvshl x y) (bvnot y) = literal n 0 := by
  rcases large_or_bvnot_large y with h | h
  · rw [bvshl_large x y h]; simp [bvshl_eq_shiftLeft, literal]
  · exact bvshl_large _ _ h

theorem bv_term_small_rw_1256 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvshl s s) (bvnot s)) = (literal n 0) := by
  intro n s t
  simp only [bvshl_bvshl_bvnot]

end BV.QF_BV.Unsat
