/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1540.smt2
License: CC BY 4.0
-/
import Init.Data.Nat.MinMax
import LEMMAS_learned.BitVec.Shift.Basic
import LEMMAS_learned.Nat.Pow
import SMT.BitVec.ToNat.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvlshr_bvmul_same (x y : BitVec n) :
    bvlshr (bvlshr (bvmul x x) x) y = bvlshr (bvmul x (bvlshr x y)) x := by
  by_cases hy : y = literal n 0
  · rw [hy, bvlshr_zero, bvlshr_zero]
  have hy0 : 0 < y.toNat := by
    apply Nat.pos_of_ne_zero
    intro h; apply hy; apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using h
  have hp : 2 ≤ 2 ^ y.toNat := Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hy0)
  have hs := Learned.Nat.sq_lt_two_pow_succ x.toNat
  rw [Nat.pow_succ] at hs
  have hq := Nat.div_mul_le_self x.toNat (2 ^ y.toNat)
  have hq2 := Nat.mul_le_mul_left (x.toNat / 2 ^ y.toNat) hp
  have hq3 : (x.toNat / 2 ^ y.toNat) * 2 ≤ x.toNat := by omega
  have hmul := Nat.mul_le_mul_left x.toNat hq3
  rw [← Nat.mul_assoc] at hmul
  have hr : bvlshr (bvmul x (bvlshr x y)) x = literal n 0 := by
    apply bvlshr_eq_zero_of_lt
    rw [toNat_bvmul, toNat_bvlshr]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  rw [hr]
  apply toNat_injective
  simp only [toNat_bvlshr, toNat_bvmul, toNat_literal, Nat.zero_mod]
  rw [Nat.div_div_eq_div_mul]
  apply Nat.div_eq_of_lt
  apply Nat.lt_of_le_of_lt (Nat.mod_le _ _)
  have hm := Nat.mul_le_mul_left (2 ^ x.toNat) hp
  omega

theorem bv_term_small_rw_1540 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvlshr (bvmul s s) s) t) = (bvlshr (bvmul s (bvlshr s t)) s) := by
  intro n s t
  exact bvlshr_bvlshr_bvmul_same s t

end BV.QF_BV.Unsat
