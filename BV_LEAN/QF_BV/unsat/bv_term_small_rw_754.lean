/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_754.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvand_bvshl_bvlshr_swap (x y : BitVec n) :
    bvand x (bvshl (bvlshr y x) y) = literal n 0 := by
  rcases Nat.le_total x.toNat y.toNat with h | h
  · apply bvand_bvshl_eq_zero_of_lt
    exact Nat.lt_of_le_of_lt h Nat.lt_two_pow_self
  · rw [bvlshr_eq_zero_of_le y x h]
    simp [bvshl_eq_shiftLeft, bvand, literal]

theorem bv_term_small_rw_754 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand s (bvshl (bvlshr t s) t)) = (literal n 0) := by
  intro n s t
  simp only [bvand_bvshl_bvlshr_swap]

end BV.QF_BV.Unsat
