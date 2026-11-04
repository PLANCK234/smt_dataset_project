/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local derivations from Lean 4.34.1 Init and the SMT API.
Source dependencies and pinned revisions: upstream.json.
-/
module
prelude

public import LEMMAS_learned.BitVec.Shift.Bounds

@[expose] public section

namespace Learned.BitVec
open SMT.BitVec

/-- A nonzero self-shift has a negation large enough to clear any n-bit word. -/
theorem width_le_toNat_bvneg_bvshl_self (x : _root_.BitVec n)
    (hb : bvshl x x ≠ literal n 0) : n ≤ (bvneg (bvshl x x)).toNat := by
  have hb0 : 0 < (bvshl x x).toNat := by
    apply Nat.pos_of_ne_zero
    intro h
    apply hb
    apply toNat_injective
    simpa only [toNat_literal, Nat.zero_mod] using h
  have hb_lt := (bvshl x x).isLt
  have hc : (bvneg (bvshl x x)).toNat = 2 ^ n - (bvshl x x).toNat := by
    rw [toNat_bvneg, Nat.mod_eq_of_lt (by omega)]
  by_cases ha : n ≤ 2 ^ x.toNat
  · -- Both b and -b are multiples of 2^a; -b is a positive one.
    have hd : 2 ^ x.toNat ∣ (bvneg (bvshl x x)).toNat := by
      rw [← Learned.BitVec.bvshl_bvneg]
      exact Learned.BitVec.two_pow_dvd_toNat_bvshl (bvneg x) x
    exact Nat.le_trans ha (Nat.le_of_dvd (by rw [hc]; omega) hd)
  · -- If 2^a < n, then 2a ≤ 2^a ≤ n-1 and a*2^a < 2^(n-1).
    have htwice := Learned.Nat.two_mul_le_two_pow (n := x.toNat)
    have hproduct : x.toNat * 2 ^ x.toNat < 2 ^ (n - 1) := by
      calc
        x.toNat * 2 ^ x.toNat < 2 ^ x.toNat * 2 ^ x.toNat :=
          Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.two_pow_pos _)
        _ = 2 ^ (x.toNat + x.toNat) := (Nat.pow_add ..).symm
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hb_half : (bvshl x x).toNat < 2 ^ (n - 1) := by
      rw [toNat_bvshl]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hproduct
    have hpow_pos := Nat.two_pow_pos x.toNat
    have hn : n = (n - 1) + 1 := by omega
    have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
      conv => lhs; rw [hn, Nat.pow_succ]
    have hwidth := Learned.Nat.two_mul_le_two_pow (n := n)
    rw [hc]
    omega

/-- A complemented word shifted by its original value is either zero or at least the width. -/
theorem width_le_toNat_bvshl_bvnot_self (x : _root_.BitVec n)
    (hb : bvshl (bvnot x) x ≠ literal n 0) : n ≤ (bvshl (bvnot x) x).toNat := by
  by_cases ha : n ≤ 2 ^ x.toNat
  · have hb0 : 0 < (bvshl (bvnot x) x).toNat := by
      apply Nat.pos_of_ne_zero
      intro h
      apply hb
      apply toNat_injective
      simpa only [toNat_literal, Nat.zero_mod] using h
    exact Nat.le_trans ha (Nat.le_of_dvd hb0 (Learned.BitVec.two_pow_dvd_toNat_bvshl (bvnot x) x))
  · have hx := x.isLt
    have hself := Nat.lt_two_pow_self (n := x.toNat)
    have hn := Nat.lt_two_pow_self (n := n)
    have hpowpos := Nat.two_pow_pos x.toNat
    have htwice := Learned.Nat.two_mul_le_two_pow (n := x.toNat)
    have hprod : (x.toNat + 1) * 2 ^ x.toNat ≤ 2 ^ (n - 1) := by
      calc
        (x.toNat + 1) * 2 ^ x.toNat ≤ 2 ^ x.toNat * 2 ^ x.toNat :=
          Nat.mul_le_mul_right _ hself
        _ = 2 ^ (x.toNat + x.toNat) := (Nat.pow_add ..).symm
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
      conv => lhs; rw [show n = (n - 1) + 1 by omega, Nat.pow_succ]
    have hhalfpos := Nat.two_pow_pos (n - 1)
    have hval : (bvneg (bvnot x)).toNat = x.toNat + 1 := by
      rw [toNat_bvneg, toNat_bvnot,
        show 2 ^ n - (2 ^ n - 1 - x.toNat) = x.toNat + 1 by omega,
        Nat.mod_eq_of_lt (by omega)]
    have he : bvshl (bvnot x) x = bvneg (bvshl (bvneg (bvnot x)) x) := by
      rw [← Learned.BitVec.bvshl_bvneg, bvneg_bvneg]
    have hbval : (bvshl (bvneg (bvnot x)) x).toNat = (x.toNat + 1) * 2 ^ x.toNat := by
      rw [toNat_bvshl, hval, Nat.mod_eq_of_lt (by omega)]
    have hprodpos : 0 < (x.toNat + 1) * 2 ^ x.toNat := Nat.mul_pos (by omega) hpowpos
    have hwidth := Learned.Nat.two_mul_le_two_pow (n := n)
    rw [he, toNat_bvneg, hbval, Nat.mod_eq_of_lt (by omega)]
    omega

end Learned.BitVec
