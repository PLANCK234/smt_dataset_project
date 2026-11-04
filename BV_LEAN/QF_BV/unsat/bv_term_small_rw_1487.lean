/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1487.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import LEMMAS_learned.Nat.Div
import SMT.BitVec.ToNat.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvshl_bvlshr_swap (x y : BitVec n) :
    bvlshr (bvshl x (bvlshr y x)) y = bvlshr x y := by
  rcases Nat.le_total x.toNat y.toNat with h | h
  · rw [bvlshr_eq_zero_of_le x y h]
    apply bvlshr_eq_zero_of_lt
    rw [toNat_bvshl, toNat_bvlshr]
    apply Nat.lt_of_le_of_lt (Nat.mod_le _ _)
    have hb := Learned.Nat.add_div_two_pow_le_max y.toNat x.toNat
    have he : x.toNat + y.toNat / 2 ^ x.toNat ≤ y.toNat := by omega
    apply Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right (Nat.lt_two_pow_self (n := x.toNat)) (Nat.two_pow_pos _))
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) he
  · rw [bvlshr_eq_zero_of_le y x h, bvshl_zero]

theorem bv_term_small_rw_1487 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvshl s (bvlshr t s)) t) = (bvlshr s t) := by
  intro n s t
  exact bvlshr_bvshl_bvlshr_swap s t

end BV.QF_BV.Unsat
