/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local derivations from Lean 4.34.1 Init and the SMT API.
Source dependencies and pinned revisions: upstream.json.
-/
module
prelude

public import LEMMAS_learned.BitVec.Shift.Conditions
public import LEMMAS_learned.Nat.Mod

@[expose] public section

namespace Learned.BitVec
open SMT.BitVec

theorem bvshl_eq_bvlshr_iff_dvd (x y : _root_.BitVec n) :
    bvshl x y = bvlshr x y ↔
      2 ^ (n + y.toNat) ∣
        (2 ^ (y.toNat + y.toNat) - 1) * x.toNat + x.toNat % 2 ^ y.toNat := by
  let a := x.toNat
  let e := 2 ^ y.toNat
  let p := 2 ^ n
  have he : 0 < e := Nat.two_pow_pos _
  have hp : 0 < p := Nat.two_pow_pos _
  have ha : a < p := x.isLt
  have hdiv := Nat.div_add_mod a e
  have hmul : a ≤ a * (e * e) := Nat.le_mul_of_pos_right _ (Nat.mul_pos he he)
  have hR : e * (a / e) < p * e := by
    have hle : p ≤ p * e := Nat.le_mul_of_pos_right _ he
    omega
  have hD : (e * e - 1) * a + a % e = e * (a * e) - e * (a / e) := by
    rw [Nat.sub_mul, Nat.one_mul]
    have hc : e * e * a = e * (a * e) := by simp only [Nat.mul_comm, Nat.mul_left_comm]
    have hc' : a * (e * e) = e * (a * e) := by simp only [Nat.mul_left_comm]
    rw [hc] at *
    rw [hc'] at hmul
    omega
  have htotal : a ≤ e * (a * e) := by
    calc
      a ≤ a * (e * e) := hmul
      _ = e * (a * e) := by simp only [Nat.mul_left_comm]
  rw [eq_iff_toNat_eq, toNat_bvshl, toNat_bvlshr, Nat.pow_add, Nat.pow_add]
  change (a * e) % p = a / e ↔ p * e ∣ (e * e - 1) * a + a % e
  rw [hD, ← Learned.Nat.mod_eq_iff_dvd_sub_of_le hR (by omega)]
  rw [Nat.mul_comm p e, Nat.mul_mod_mul_left]
  exact ⟨congrArg (fun z => e * z), Nat.mul_left_cancel he⟩

theorem bvand_bvshl_eq_zero_iff_bvand_bvlshr_eq_zero (x y z : _root_.BitVec n) :
    bvand x (bvshl y z) = literal n 0 ↔ bvand y (bvlshr x z) = literal n 0 := by
  constructor
  · intro h
    rw [Learned.BitVec.bvand_bvlshr_eq_bvlshr_bvand_bvshl, h]
    simp [bvlshr, literal]
  · intro h
    have he := congrArg (fun w => bvshl w z) h
    have hid : bvshl (bvand y (bvlshr x z)) z = bvand x (bvshl y z) := by
      simp only [bvshl_eq_shiftLeft, bvand, bvlshr, _root_.BitVec.shiftLeft_eq', _root_.BitVec.ushiftRight_eq',
        _root_.BitVec.shiftLeft_and_distrib, _root_.BitVec.shiftLeft_ushiftRight]
      rw [← _root_.BitVec.and_assoc, _root_.BitVec.and_comm (y <<< z.toNat) x,
        _root_.BitVec.and_assoc, _root_.BitVec.and_comm (y <<< z.toNat),
        _root_.BitVec.allOnes_shiftLeft_and_shiftLeft]
    rw [hid] at he
    simpa [bvshl_eq_shiftLeft, literal] using he

/-- The unique inner-count mismatch: a top bit doubles to zero. -/
theorem bvshl_bvnot_self_top_obstruction (x : BitVec n) (hhalf : (bvshl x (bvnot x)).toNat = 2 ^ (n - 1)) :
    n ≤ (bvshl x (bvnot x)).toNat ∧ bvshl x (bvneg x) = literal n 0 ∧ x ≠ literal n 0 := by
  have ha : bvshl x (bvnot x) ≠ literal n 0 := by
    intro he
    have hh := congrArg _root_.BitVec.toNat he
    simp only [toNat_literal, Nat.zero_mod] at hh
    have := Nat.two_pow_pos (n - 1)
    omega
  have hn : n ≠ 0 := by
    intro hz
    have hh := (bvshl x (bvnot x)).isLt
    simp only [hz, Nat.zero_sub, Nat.pow_zero] at hh hhalf
    omega
  have hp : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv => lhs; rw [show n = n - 1 + 1 by omega, Nat.pow_succ]
  have hwidth := Learned.BitVec.width_le_toNat_bvshl_bvnot_self (bvnot x) (by simpa only [bvnot_bvnot] using ha)
  simp only [bvnot_bvnot] at hwidth
  refine ⟨hwidth, ?_, ?_⟩
  · rw [← Learned.BitVec.bvshl_bvadd_self_bvnot_same, Learned.BitVec.bvshl_bvadd]
    apply toNat_injective
    rw [toNat_bvadd, hhalf, toNat_literal, Nat.zero_mod]
    rw [show 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n by omega, Nat.mod_self]
  · intro hx
    apply ha
    rw [hx]
    simp [bvshl_eq_shiftLeft, literal]

end Learned.BitVec
