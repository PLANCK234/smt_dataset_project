/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1494.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

/-
数学分析：
令 a = s.toNat，d = t.toNat，b = t << s。b = 0 时两边都是 s << t。
若 b ≠ 0，则 b.toNat ≥ 2^a > a，左侧先右移即为零。
若 d ≥ n，右侧左移为零；若 2^a ≥ n，则 b.toNat ≥ n，右侧右移为零。
剩余分支 d < n 且 2^a < n，由 d*2^a ≤ (n-1)^2 < 2^n 知 b 不溢出。
因为 d > 0 且 2^a ≥ a+1，有 b.toNat = d*2^a ≥ a+d。
因此 (s << t).toNat ≤ a*2^d < 2^(a+d) ≤ 2^(b.toNat)，右侧为零。
-/

theorem bv_term_small_rw_1494 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvlshr s (bvshl t s)) t) = (bvlshr (bvshl s t) (bvshl t s)) := by
  intro n s t
  by_cases hb : bvshl t s = literal n 0
  · rw [hb, bvlshr_zero, bvlshr_zero]
  have hb0 : 0 < (bvshl t s).toNat := by
    apply Nat.pos_of_ne_zero
    intro h
    apply hb
    apply toNat_injective
    simpa only [toNat_literal, Nat.zero_mod] using h
  have hbpow : 2 ^ s.toNat ≤ (bvshl t s).toNat :=
    Nat.le_of_dvd hb0 (two_pow_dvd_toNat_bvshl t s)
  have hz : bvlshr s (bvshl t s) = literal n 0 :=
    bvlshr_eq_zero_of_le _ _ (Nat.le_of_lt (lt_toNat_bvshl_of_ne_zero s t hb))
  rw [hz]
  have hzsh : bvshl (literal n 0) t = literal n 0 := by simp [bvshl_eq_shiftLeft, literal]
  rw [hzsh]
  symm
  by_cases ht : n ≤ t.toNat
  · rw [bvshl_large s t ht]
    simp [bvlshr, literal]
  by_cases hp : n ≤ 2 ^ s.toNat
  · exact bvlshr_large _ _ (Nat.le_trans hp hbpow)
  have hnpos := Nat.two_pow_pos s.toNat
  have hsq := Learned.Nat.sq_lt_two_pow_succ (n - 1)
  rw [show n - 1 + 1 = n by omega] at hsq
  have hmul : t.toNat * 2 ^ s.toNat ≤ (n - 1) * (n - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hbval : (bvshl t s).toNat = t.toNat * 2 ^ s.toNat := by
    rw [toNat_bvshl, Nat.mod_eq_of_lt (by omega)]
  have htpos : 0 < t.toNat := by
    by_cases h : t.toNat = 0
    · rw [hbval, h, Nat.zero_mul] at hb0
      omega
    · omega
  have hprod := Nat.mul_le_mul_left t.toNat (Nat.lt_two_pow_self (n := s.toNat))
  rw [Nat.mul_succ] at hprod
  have hat := Nat.mul_le_mul_right s.toNat htpos
  simp only [Nat.one_mul] at hat
  have hab : s.toNat + t.toNat ≤ (bvshl t s).toNat := by
    rw [hbval]
    omega
  apply bvlshr_eq_zero_of_lt
  rw [toNat_bvshl]
  calc
    (s.toNat * 2 ^ t.toNat) % 2 ^ n ≤ s.toNat * 2 ^ t.toNat := Nat.mod_le _ _
    _ < 2 ^ s.toNat * 2 ^ t.toNat :=
      Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.two_pow_pos _)
    _ = 2 ^ (s.toNat + t.toNat) := (Nat.pow_add ..).symm
    _ ≤ 2 ^ (bvshl t s).toNat := Nat.pow_le_pow_right (by decide) hab

end BV.QF_BV.Unsat
