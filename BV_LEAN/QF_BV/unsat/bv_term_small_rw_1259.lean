/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1259.smt2
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

/-
数学分析：
令 a = s.toNat。若 a ≥ n，两侧相应的移位均被清零。
若 a < n，由 a^2 < 2^(a+1) ≤ 2^n 以及 2a < 2^n，平方移位量与倍增加法均不溢出。
分别检查 a = 0、1、2：结果依次为 0、1、0；a = 1 分支已有 n ≥ 2。
若 a ≥ 3，由 2(a-1) ≤ 2^(a-1) 得 2a < 2^a，故右侧倍增后右移为零。
又 a^2 ≥ 2a，而 (s << s).toNat ≤ a*2^a < 2^(2a) ≤ 2^(a^2)，左侧也为零。
-/

theorem bv_term_small_rw_1259 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvshl s s) (bvmul s s)) = (bvand s (bvlshr (bvadd s s) s)) := by
  intro n s _t
  by_cases hn : n ≤ s.toNat
  · rw [bvshl_large s s hn, bvlshr_large (bvadd s s) s hn, bvand_zero]
    simp [bvlshr, literal]
  have hpow : 2 ^ (s.toNat + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
  have hsq : s.toNat * s.toNat < 2 ^ n :=
    Nat.lt_of_lt_of_le (Learned.Nat.sq_lt_two_pow_succ s.toNat) hpow
  have hnwidth := Learned.Nat.two_mul_le_two_pow (n := n)
  have hdouble : s.toNat + s.toNat < 2 ^ n := by omega
  apply toNat_injective
  simp only [toNat_bvlshr, toNat_bvshl, toNat_bvmul, toNat_bvand, toNat_bvadd]
  rw [Nat.mod_eq_of_lt hsq, Nat.mod_eq_of_lt hdouble]
  rcases (show s.toNat = 0 ∨ s.toNat = 1 ∨ s.toNat = 2 ∨ 3 ≤ s.toNat by omega) with h | h | h | h
  · simp [h]
  · have hp : 4 ≤ 2 ^ n := by
      exact Nat.le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega))
    simp [h, Nat.mod_eq_of_lt (show 2 < 2 ^ n by omega)]
  · change (s.toNat * 2 ^ s.toNat % 2 ^ n) / 2 ^ (s.toNat * s.toNat) =
      s.toNat &&& ((s.toNat + s.toNat) / 2 ^ s.toNat)
    rw [h]
    change (8 % 2 ^ n) / 16 = 0
    exact Nat.div_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by decide))
  · have hprev := Learned.Nat.two_mul_le_two_pow (n := s.toNat - 1)
    have hp : 2 ^ s.toNat = 2 ^ (s.toNat - 1) * 2 := by
      conv => lhs; rw [show s.toNat = (s.toNat - 1) + 1 by omega, Nat.pow_succ]
    have hsmall : s.toNat + s.toNat < 2 ^ s.toNat := by omega
    have hmul := Nat.mul_le_mul_left s.toNat (show 2 ≤ s.toNat by omega)
    have hexp : s.toNat + s.toNat ≤ s.toNat * s.toNat := by omega
    have hzero : (s.toNat * 2 ^ s.toNat) % 2 ^ n < 2 ^ (s.toNat * s.toNat) := by
      calc
        (s.toNat * 2 ^ s.toNat) % 2 ^ n ≤ s.toNat * 2 ^ s.toNat := Nat.mod_le _ _
        _ < 2 ^ s.toNat * 2 ^ s.toNat :=
          Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.two_pow_pos _)
        _ = 2 ^ (s.toNat + s.toNat) := (Nat.pow_add ..).symm
        _ ≤ 2 ^ (s.toNat * s.toNat) := Nat.pow_le_pow_right (by decide) hexp
    rw [Nat.div_eq_of_lt hzero, Nat.div_eq_of_lt hsmall, Nat.and_zero]

end BV.QF_BV.Unsat
