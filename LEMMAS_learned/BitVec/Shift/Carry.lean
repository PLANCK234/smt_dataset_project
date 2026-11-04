/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local derivations from Lean 4.34.1 Init and the SMT API.
Source dependencies and pinned revisions: upstream.json.
-/
module
prelude

public import Init.Data.BitVec.Bitblast
public import LEMMAS_learned.BitVec.Arithmetic
public import LEMMAS_learned.BitVec.Shift.Bounds

@[expose] public section

namespace Learned.BitVec
open SMT.BitVec

/-- A shift by the mask value is beyond every set bit of that mask. -/
theorem bvand_bvadd_bvshl (x y z : _root_.BitVec n) :
    bvand x (bvadd y (bvshl z x)) = bvand x y := by
  by_cases hn : n ≤ x.toNat
  · rw [bvshl_large z x hn, bvadd_zero]
  apply toNat_injective
  rw [toNat_bvand, toNat_bvand, toNat_bvadd]
  apply Learned.Nat.and_eq_of_mod_two_pow_eq (k := x.toNat) Nat.lt_two_pow_self
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_of_lt (Nat.lt_of_not_ge hn))),
    Nat.add_mod, Nat.mod_eq_zero_of_dvd (Learned.BitVec.two_pow_dvd_toNat_bvshl z x), Nat.add_zero,
    Nat.mod_mod]

theorem bvadd_bvor_bvshl (x y z : _root_.BitVec n) :
    bvadd (bvor x y) (bvshl z x) = bvor x (bvadd y (bvshl z x)) := by
  apply (_root_.BitVec.add_right_inj (bvand x y)).mp
  change bvadd (bvand x y) (bvadd (bvor x y) (bvshl z x)) =
    bvadd (bvand x y) (bvor x (bvadd y (bvshl z x)))
  rw [← Learned.BitVec.bvand_bvadd_bvshl x y z, Learned.BitVec.bvadd_bvand_bvor,
    Learned.BitVec.bvand_bvadd_bvshl, ← bvadd_assoc, Learned.BitVec.bvadd_bvand_bvor, bvadd_assoc]

theorem bvadd_bvand_double (x y : _root_.BitVec n) :
    bvadd (bvand x y) (bvand x y) = bvand (bvadd x x) (bvadd y y) := by
  simp only [← Learned.BitVec.bvshl_one, bvshl_bvand]

theorem bvadd_bvor_double (x y : _root_.BitVec n) :
    bvadd (bvor x y) (bvor x y) = bvor (bvadd x x) (bvadd y y) := by
  simp only [← Learned.BitVec.bvshl_one, bvshl_bvor]

theorem bvadd_self_eq_shiftLeft_one (x : _root_.BitVec n) :
    bvadd x x = x <<< (1 : Nat) := by
  apply toNat_injective
  simp [bvadd, _root_.BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_two]

theorem bvand_bvnot_bvadd_self (x : _root_.BitVec n) :
    bvand (bvnot x) (bvadd x x) = bvand (bvneg x) (bvadd x x) := by
  rw [Learned.BitVec.bvadd_self_eq_shiftLeft_one]
  apply _root_.BitVec.eq_of_getElem_eq
  intro i hi
  simp only [bvand, bvnot, bvneg, _root_.BitVec.getElem_and, _root_.BitVec.getElem_not,
    _root_.BitVec.getElem_neg, _root_.BitVec.getElem_shiftLeft]
  by_cases hi0 : i = 0
  · subst i; simp
  by_cases hx : x[i - 1] = true
  · have he : ∃ j < i, x.getLsbD j = true := by
      exact ⟨i - 1, by omega, by rw [_root_.BitVec.getLsbD_eq_getElem (by omega)]; exact hx⟩
    simp [he, hx]
  · have hf : x[i - 1] = false := by cases h : x[i - 1] <;> simp_all
    simp [hf]

theorem bvand_bvshl_bvneg_of_ne_zero (x y : _root_.BitVec n) (hy : y ≠ literal n 0) :
    bvand y (bvshl x (bvneg y)) = bvshl x (bvneg y) := by
  have hy0 : 0 < y.toNat := by
    apply Nat.pos_of_ne_zero
    intro h; apply hy; apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using h
  have hlt := y.isLt
  have hp := Nat.two_pow_pos n
  have hb : (bvnot y).toNat < 2 ^ (bvneg y).toNat := by
    rw [toNat_bvnot, toNat_bvneg, Nat.mod_eq_of_lt (by omega)]
    have := Nat.lt_two_pow_self (n := 2 ^ n - y.toNat)
    omega
  have hd := Learned.BitVec.bvand_bvshl_eq_zero_of_lt (bvnot y) x (bvneg y) hb
  rw [bvand_comm] at hd
  have h := Learned.BitVec.bvand_bvnot_of_bvand_eq_zero _ _ hd
  simpa only [bvnot_bvnot, bvand_comm] using h

theorem bvshl_bvadd_self_bvnot (x y : _root_.BitVec n) :
    bvshl (bvadd x x) (bvnot y) = bvand y (bvshl x (bvneg y)) := by
  by_cases hy : y = literal n 0
  · subst y; rw [Learned.BitVec.bvshl_bvnot_zero, bvand_comm, bvand_zero]
  have hy0 : 0 < y.toNat := by
    apply Nat.pos_of_ne_zero
    intro h; apply hy; apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using h
  have hlt := y.isLt
  have hp := Nat.two_pow_pos n
  have hn : (bvnot y).toNat + 1 = (bvneg y).toNat := by
    rw [toNat_bvnot, toNat_bvneg, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [Learned.BitVec.bvand_bvshl_bvneg_of_ne_zero x y hy, Learned.BitVec.bvadd_self_eq_shiftLeft_one]
  simp only [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq', ← _root_.BitVec.shiftLeft_add]
  rw [Nat.add_comm 1, hn]

theorem bvshl_bvadd_self_bvnot_same (x : _root_.BitVec n) :
    bvshl (bvadd x x) (bvnot x) = bvshl x (bvneg x) := by
  rw [Learned.BitVec.bvshl_bvadd_self_bvnot, Learned.BitVec.bvand_bvshl_self_bvneg]

end Learned.BitVec
