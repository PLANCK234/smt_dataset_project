/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local derivations from Lean 4.34.1 Init and the SMT API.
Source dependencies and pinned revisions: upstream.json.
-/
module
prelude

public import Init.Data.Nat.MinMax
public import LEMMAS_learned.BitVec.Shift.Basic
public import LEMMAS_learned.Nat.Pow
public import SMT.BitVec.ToNat.Arithmetic

@[expose] public section

namespace Learned.BitVec
open SMT.BitVec

theorem width_le_toNat_bvnot_bvlshr (x y : _root_.BitVec n)
    (hx : x ≠ literal n 0) : n ≤ (bvnot (bvlshr y x)).toNat := by
  have hx0 : 0 < x.toNat := by
    have hz : x.toNat ≠ 0 := by
      intro h; apply hx; apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using h
    omega
  have hp : 2 ≤ 2 ^ x.toNat := by
    exact Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hx0)
  have hq := Nat.div_mul_le_self y.toNat (2 ^ x.toNat)
  have hq2 := Nat.mul_le_mul_left (y.toNat / 2 ^ x.toNat) hp
  have hn := Learned.Nat.two_mul_le_two_pow (n := n)
  have hy := y.isLt
  rw [toNat_bvnot, toNat_bvlshr]
  omega

theorem bvlshr_bvneg_self_of_ne_zero (x : _root_.BitVec n) (hx : x ≠ literal n 0) :
    bvlshr (bvneg x) x = bvlshr (bvnot x) x := by
  by_cases hn : n ≤ x.toNat
  · rw [Learned.BitVec.bvlshr_large _ _ hn, Learned.BitVec.bvlshr_large _ _ hn]
  have hx0 : 0 < x.toNat := by
    apply Nat.pos_of_ne_zero
    intro h; apply hx; apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using h
  have hlt := x.isLt
  have hp : 2 ^ n = 2 ^ x.toNat * 2 ^ (n - x.toNat) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hn))]
  have hxpow : x.toNat < 2 ^ x.toNat := Nat.lt_two_pow_self
  have hm : x.toNat - 1 < 2 ^ x.toNat := by omega
  apply toNat_injective
  simp only [toNat_bvlshr, toNat_bvneg, toNat_bvnot]
  rw [Nat.mod_eq_of_lt (by omega), hp]
  rw [show 2 ^ x.toNat * 2 ^ (n - x.toNat) - x.toNat =
    2 ^ x.toNat * 2 ^ (n - x.toNat) - (x.toNat - 1 + 1) by omega]
  rw [Nat.mul_sub_div _ _ _ (by omega), Nat.div_eq_of_lt hm]
  rw [show 2 ^ x.toNat * 2 ^ (n - x.toNat) - 1 - x.toNat =
    2 ^ x.toNat * 2 ^ (n - x.toNat) - (x.toNat + 1) by omega]
  rw [Nat.mul_sub_div _ _ _ (by omega), Nat.div_eq_of_lt hxpow]

theorem bvadd_bvlshr_self_lt_two_pow (x y : _root_.BitVec n)
    (hy : y ≠ literal n 0) : x.toNat + (bvlshr x y).toNat < 2 ^ x.toNat := by
  have hy0 : 0 < y.toNat := by
    apply Nat.pos_of_ne_zero
    intro h; apply hy; apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using h
  have hp : 2 ≤ 2 ^ y.toNat := Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hy0)
  rw [toNat_bvlshr]
  have hq := Nat.div_mul_le_self x.toNat (2 ^ y.toNat)
  have hq2 := Nat.mul_le_mul_left (x.toNat / 2 ^ y.toNat) hp
  have hn := Learned.Nat.two_mul_le_two_pow (n := x.toNat)
  by_cases hx : x.toNat = 0
  · simp [hx]
  · omega

theorem width_le_toNat_bvshl_bvnot_zero (y : _root_.BitVec n) (hy : y.toNat < n) :
    n ≤ (bvshl (bvnot (literal n 0)) y).toNat := by
  have hp : 2 ^ y.toNat < 2 ^ n := Nat.pow_lt_pow_right (by decide) hy
  have hp0 := Nat.two_pow_pos y.toNat
  have hd : 2 ^ y.toNat * 2 ≤ 2 ^ n := by
    rw [← Nat.pow_succ]
    exact Nat.pow_le_pow_right (by decide) hy
  have hn := Learned.Nat.two_mul_le_two_pow (n := n)
  have he : bvshl (bvnot (literal n 0)) y = bvneg (bvshl (literal n 1) y) := by
    rw [← Learned.BitVec.bvshl_bvneg]
    congr 1
    simpa only [bvnot, bvneg, literal, _root_.BitVec.not_zero] using (_root_.BitVec.neg_one_eq_allOnes (w := n)).symm
  have hv : (bvshl (literal n 1) y).toNat = 2 ^ y.toNat := by
    rw [toNat_bvshl, toNat_literal, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega)),
      Nat.one_mul, Nat.mod_eq_of_lt hp]
  rw [he, toNat_bvneg, hv, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A nonzero quotient after a positive right shift has a large modular negation. -/
theorem width_le_toNat_bvneg_bvlshr (x y : _root_.BitVec n)
    (hx : x ≠ literal n 0) (hq : bvlshr y x ≠ literal n 0) :
    n ≤ (bvneg (bvlshr y x)).toNat := by
  have hn := Learned.BitVec.width_le_toNat_bvnot_bvlshr x y hx
  have hq0 : 0 < (bvlshr y x).toNat := by
    apply Nat.pos_of_ne_zero
    intro h
    apply hq
    apply toNat_injective
    simpa only [toNat_literal, Nat.zero_mod] using h
  have hlt := (bvlshr y x).isLt
  rw [toNat_bvnot] at hn
  rw [toNat_bvneg, Nat.mod_eq_of_lt (by omega)]
  omega

end Learned.BitVec
