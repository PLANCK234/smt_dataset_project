/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1491.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

/-
Proof sketch:
Let a = s.toNat and b = t << s. If b = 0 both sides are s << s.
If b ≠ 0, 2^a divides b.toNat, so b.toNat ≥ 2^a > a and s >> b = 0.
Also (s << s).toNat ≤ a*2^a < 2^(2a) and 2a ≤ 2^a ≤ b.toNat,
so (s << s).toNat < 2^(b.toNat) and the right side is zero.
-/

theorem bv_term_small_rw_1491 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvlshr s (bvshl t s)) s) = (bvlshr (bvshl s s) (bvshl t s)) := by
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
  have hzsh : bvshl (literal n 0) s = literal n 0 := by simp [bvshl_eq_shiftLeft, literal]
  rw [hzsh]
  symm
  apply bvlshr_eq_zero_of_lt
  rw [toNat_bvshl]
  have htwice := Learned.Nat.two_mul_le_two_pow (n := s.toNat)
  calc
    (s.toNat * 2 ^ s.toNat) % 2 ^ n ≤ s.toNat * 2 ^ s.toNat := Nat.mod_le _ _
    _ < 2 ^ s.toNat * 2 ^ s.toNat :=
      Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.two_pow_pos _)
    _ = 2 ^ (s.toNat + s.toNat) := (Nat.pow_add ..).symm
    _ ≤ 2 ^ (bvshl t s).toNat := Nat.pow_le_pow_right (by decide) (by omega)

end BV.QF_BV.Unsat
