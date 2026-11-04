/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local derivations from Lean 4.34.1 Init and the SMT API.
Source dependencies and pinned revisions: upstream.json.
-/
module
prelude

public import LEMMAS_learned.BitVec.Shift.Basic
public import LEMMAS_learned.Nat.Div
public import LEMMAS_learned.Nat.Pow
public import SMT.BitVec.ToNat.Arithmetic

@[expose] public section

namespace Learned.BitVec
open SMT.BitVec

theorem large_or_bvnot_large (y : _root_.BitVec n) :
    n ≤ y.toNat ∨ n ≤ (bvnot y).toNat := by
  have h := @Learned.Nat.two_mul_le_two_pow n
  rw [toNat_bvnot]
  omega

theorem large_or_bvneg_large (y : _root_.BitVec n) (hy : y ≠ literal n 0) :
    n ≤ y.toNat ∨ n ≤ (bvneg y).toNat := by
  have h := @Learned.Nat.two_mul_le_two_pow n
  have hyp : 0 < y.toNat := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hy
    apply toNat_injective
    simpa only [toNat_literal, Nat.zero_mod] using hz
  have hylt := y.isLt
  rw [toNat_bvneg, Nat.mod_eq_of_lt (by omega)]
  omega

theorem two_pow_dvd_toNat_bvshl (x y : _root_.BitVec n) :
    2 ^ y.toNat ∣ (bvshl x y).toNat := by
  by_cases h : n ≤ y.toNat
  · rw [bvshl_large x y h, toNat_literal, Nat.zero_mod]
    exact Nat.dvd_zero _
  · rw [toNat_bvshl]
    apply (Nat.dvd_mod_iff (Nat.pow_dvd_pow 2 (by omega))).mpr
    exact Nat.dvd_mul_left _ _

theorem lt_toNat_bvshl_of_ne_zero (x y : _root_.BitVec n)
    (h : bvshl y x ≠ literal n 0) : x.toNat < (bvshl y x).toNat := by
  have hp : 0 < (bvshl y x).toNat := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply h
    apply toNat_injective
    simpa only [toNat_literal, Nat.zero_mod] using hz
  exact Nat.lt_of_lt_of_le Nat.lt_two_pow_self
    (Nat.le_of_dvd hp (Learned.BitVec.two_pow_dvd_toNat_bvshl y x))

theorem bvlshr_bvshl_self_eq_ite (x y : _root_.BitVec n) :
    bvlshr x (bvshl y x) = if bvshl y x = literal n 0 then x else literal n 0 := by
  split
  · rename_i h
    rw [h, bvlshr_zero]
  · rename_i h
    apply Learned.BitVec.bvlshr_eq_zero_of_le
    exact Nat.le_of_lt (Learned.BitVec.lt_toNat_bvshl_of_ne_zero x y h)

theorem bvshl_bvshl_comm (x y z : _root_.BitVec n) :
    bvshl (bvshl x y) z = bvshl (bvshl x z) y := by
  simp only [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq',
    ← _root_.BitVec.shiftLeft_add, Nat.add_comm]

theorem bvlshr_bvlshr_comm (x y z : _root_.BitVec n) :
    bvlshr (bvlshr x y) z = bvlshr (bvlshr x z) y := by
  simp only [bvlshr, _root_.BitVec.ushiftRight_eq',
    ← _root_.BitVec.shiftRight_add, Nat.add_comm]

theorem large_bvor_bvneg (y : _root_.BitVec n) (hy : y ≠ literal n 0) :
    n ≤ (bvor y (bvneg y)).toNat := by
  rcases Learned.BitVec.large_or_bvneg_large y hy with h | h
  · exact Nat.le_trans h SMT.Nat.left_le_or
  · exact Nat.le_trans h SMT.Nat.right_le_or

/-- At least one of two mutually shifted values vanishes. -/
theorem bvlshr_eq_zero_or (x y : _root_.BitVec n) :
    bvlshr x y = literal n 0 ∨ bvlshr y x = literal n 0 := by
  rcases Nat.le_total x.toNat y.toNat with h | h
  · exact Or.inl (Learned.BitVec.bvlshr_eq_zero_of_le x y h)
  · exact Or.inr (Learned.BitVec.bvlshr_eq_zero_of_le y x h)

theorem bvand_bvshl_self_bvneg (x : _root_.BitVec n) :
    bvand x (bvshl x (bvneg x)) = bvshl x (bvneg x) := by
  by_cases hx : x = literal n 0
  · subst x; simp [bvand, bvshl_eq_shiftLeft, literal]
  · have hp : 0 < x.toNat := by
      apply Nat.pos_of_ne_zero
      intro hz
      apply hx
      apply toNat_injective
      simpa only [toNat_literal, Nat.zero_mod] using hz
    have hlt := x.isLt
    have h : (bvnot x).toNat < 2 ^ (bvneg x).toNat := by
      rw [toNat_bvnot, toNat_bvneg, Nat.mod_eq_of_lt (by omega)]
      have := @Nat.lt_two_pow_self (2 ^ n - x.toNat)
      omega
    have hd := Learned.BitVec.bvand_bvshl_eq_zero_of_lt (bvnot x) x (bvneg x) h
    rw [bvand_comm] at hd
    have hh := Learned.BitVec.bvand_bvnot_of_bvand_eq_zero _ _ hd
    simpa only [bvnot_bvnot, bvand_comm] using hh

/-- Shift counts may be added as bitvectors when their addition has no carry. -/
theorem bvshl_bvshl_of_bvand_eq_zero (x y z : _root_.BitVec n)
    (h : bvand y z = literal n 0) :
    bvshl (bvshl x y) z = bvshl x (bvadd y z) := by
  simp only [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq',
    Learned.BitVec.toNat_bvadd_of_bvand_eq_zero y z h, _root_.BitVec.shiftLeft_add]

theorem bvlshr_bvlshr_of_bvand_eq_zero (x y z : _root_.BitVec n)
    (h : bvand y z = literal n 0) :
    bvlshr (bvlshr x y) z = bvlshr x (bvadd y z) := by
  simp only [bvlshr, _root_.BitVec.ushiftRight_eq',
    Learned.BitVec.toNat_bvadd_of_bvand_eq_zero y z h, _root_.BitVec.shiftRight_add]

/-- This sum of shift counts cannot wrap, even though the second count is symbolic. -/
theorem toNat_bvadd_bvlshr (x y : _root_.BitVec n) :
    (bvadd y (bvlshr x y)).toNat = y.toNat + (bvlshr x y).toNat := by
  rw [toNat_bvadd, toNat_bvlshr]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Learned.Nat.add_div_two_pow_le_max x.toNat y.toNat)
    (Nat.max_lt.mpr ⟨x.isLt, y.isLt⟩)

end Learned.BitVec
