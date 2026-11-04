/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1366.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvshl_bvlshr_swap (x y : BitVec n) :
    bvshl (bvlshr x y) (bvlshr y x) = bvlshr x y := by
  rcases bvlshr_eq_zero_or x y with h | h <;> rw [h] <;> simp [bvshl_eq_shiftLeft, literal]

theorem bv_term_small_rw_1366 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvlshr s t) (bvlshr t s)) = (bvlshr s t) := by
  intro n s t
  simp only [bvshl_bvlshr_swap]

end BV.QF_BV.Unsat
