/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1537.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import LEMMAS_learned.BitVec.Shift.Quotient

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvlshr_bvadd_same (x y : BitVec n) :
    bvlshr (bvlshr (bvadd x x) x) y = bvlshr (bvadd x (bvlshr x y)) x := by
  by_cases hy : y = literal n 0
  · rw [hy, bvlshr_zero, bvlshr_zero]
  have hy0 : 0 < y.toNat := by
    apply Nat.pos_of_ne_zero
    intro h; apply hy; apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using h
  have hp : 2 ≤ 2 ^ y.toNat := Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hy0)
  have hr : bvlshr (bvadd x (bvlshr x y)) x = literal n 0 := by
    apply bvlshr_eq_zero_of_lt
    rw [toNat_bvadd]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (bvadd_bvlshr_self_lt_two_pow x y hy)
  rw [hr]
  apply toNat_injective
  simp only [toNat_bvlshr, toNat_bvadd, toNat_literal, Nat.zero_mod]
  rw [Nat.div_div_eq_div_mul]
  apply Nat.div_eq_of_lt
  apply Nat.lt_of_le_of_lt (Nat.mod_le _ _)
  have hx := Nat.lt_two_pow_self (n := x.toNat)
  have hm := Nat.mul_le_mul_left (2 ^ x.toNat) hp
  omega

theorem bv_term_small_rw_1537 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvlshr (bvadd s s) t) s) = (bvlshr (bvadd s (bvlshr s t)) s) := by
  intro n s t
  rw [bvlshr_bvlshr_comm]
  exact bvlshr_bvlshr_bvadd_same s t

end BV.QF_BV.Unsat
