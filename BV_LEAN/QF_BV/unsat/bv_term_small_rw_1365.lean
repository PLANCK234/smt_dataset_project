/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1365.smt2
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

theorem bv_term_small_rw_1365 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor (bvlshr s t) (bvlshr t s)) = (bvadd (bvlshr s t) (bvlshr t s)) := by
  intro n s t
  simp only [bvand_bvlshr_swap, bvor_eq_bvadd_of_bvand_eq_zero]

end BV.QF_BV.Unsat
