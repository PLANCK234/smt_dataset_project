/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1480.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvadd_bvlshr_swap (x y : BitVec n) : bvlshr (bvadd x (bvlshr y x)) y = bvlshr x y := by
  rcases Nat.le_total x.toNat y.toNat with h | h
  · rw [bvlshr_eq_zero_of_le x y h]
    apply bvlshr_eq_zero_of_le
    rw [toNat_bvadd_bvlshr, toNat_bvlshr]
    exact Nat.le_trans (Learned.Nat.add_div_two_pow_le_max y.toNat x.toNat) (by omega)
  · rw [bvlshr_eq_zero_of_le y x h, bvadd_zero]

theorem bv_term_small_rw_1480 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvadd s (bvlshr t s)) t) = (bvlshr s t) := by
  intro n s t
  simp only [bvlshr_bvadd_bvlshr_swap]

end BV.QF_BV.Unsat
