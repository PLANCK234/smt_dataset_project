/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1423.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvshl_bvlshr_bvnot (x y : BitVec n) :
    bvshl (bvlshr x y) (bvnot y) = literal n 0 := by
  rcases large_or_bvnot_large y with h | h
  · rw [bvlshr_large x y h]; simp [bvshl_eq_shiftLeft, literal]
  · exact bvshl_large _ _ h

theorem bv_term_small_rw_1423 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvlshr s (bvnot s)) s) = (literal n 0) := by
  intro n s t
  simpa only [bvnot_bvnot] using
    bvshl_bvlshr_bvnot s (bvnot s)

end BV.QF_BV.Unsat
