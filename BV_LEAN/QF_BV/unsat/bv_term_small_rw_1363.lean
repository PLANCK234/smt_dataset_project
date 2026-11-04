/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1363.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvand_bvlshr_swap (x y : BitVec n) :
    bvand (bvlshr x y) (bvlshr y x) = literal n 0 := by
  rcases bvlshr_eq_zero_or x y with h | h <;> rw [h] <;> simp [bvand, literal]

theorem bv_term_small_rw_1363 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand (bvlshr s t) (bvlshr t s)) = (literal n 0) := by
  intro n s t
  simp only [bvand_bvlshr_swap]

end BV.QF_BV.Unsat
