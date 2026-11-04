/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local derivations from Lean 4.34.1 Init and the SMT API.
Source dependencies and pinned revisions: upstream.json.
-/
module
prelude

public import LEMMAS_learned.BitVec.Bitwise
public import SMT.BitVec.Rewrite.Shift
public import SMT.BitVec.ToNat.Basic
public import SMT.BitVec.ToNat.Bitwise
public import SMT.BitVec.ToNat.Shift

@[expose] public section

namespace Learned.BitVec
open SMT.BitVec

theorem bvlshr_self (x : _root_.BitVec n) : bvlshr x x = literal n 0 := by
  exact _root_.BitVec.ushiftRight_self x

theorem bvlshr_large (x y : _root_.BitVec n) (h : n ≤ y.toNat) :
    bvlshr x y = literal n 0 := by
  exact _root_.BitVec.ushiftRight_eq_zero h

theorem width_le_toNat_bvnot_zero : n ≤ (bvnot (literal n 0)).toNat := by
  have := Nat.lt_two_pow_self (n := n)
  simp only [toNat_bvnot, toNat_literal, Nat.zero_mod, Nat.sub_zero]
  omega

theorem bvshl_bvnot_zero (x : _root_.BitVec n) :
    bvshl x (bvnot (literal n 0)) = literal n 0 :=
  bvshl_large x _ Learned.BitVec.width_le_toNat_bvnot_zero

theorem bvlshr_bvnot_zero (x : _root_.BitVec n) :
    bvlshr x (bvnot (literal n 0)) = literal n 0 :=
  Learned.BitVec.bvlshr_large x _ Learned.BitVec.width_le_toNat_bvnot_zero

theorem bvlshr_bvand (x y z : _root_.BitVec n) :
    bvlshr (bvand x y) z = bvand (bvlshr x z) (bvlshr y z) :=
  _root_.BitVec.ushiftRight_and_distrib x y z.toNat

theorem bvlshr_bvor (x y z : _root_.BitVec n) :
    bvlshr (bvor x y) z = bvor (bvlshr x z) (bvlshr y z) :=
  _root_.BitVec.ushiftRight_or_distrib x y z.toNat

theorem bvshl_bvmul (x y z : _root_.BitVec n) :
    bvshl (bvmul x y) z = bvmul x (bvshl y z) := by
  simp only [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq', bvmul,
    _root_.BitVec.shiftLeft_eq_mul_twoPow, _root_.BitVec.mul_assoc]

theorem bvmul_bvshl_comm (x y z : _root_.BitVec n) :
    bvmul x (bvshl y z) = bvmul y (bvshl x z) := by
  rw [← Learned.BitVec.bvshl_bvmul, ← Learned.BitVec.bvshl_bvmul, bvmul_comm]

theorem bvshl_bvneg (x y : _root_.BitVec n) :
    bvshl (bvneg x) y = bvneg (bvshl x y) := by
  simp only [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq', bvneg,
    _root_.BitVec.shiftLeft_neg]

theorem bvshl_bvadd (x y z : _root_.BitVec n) :
    bvshl (bvadd x y) z = bvadd (bvshl x z) (bvshl y z) := by
  simp only [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq', bvadd,
    _root_.BitVec.shiftLeft_add_distrib]

theorem bvlshr_eq_zero_of_lt (x y : _root_.BitVec n)
    (h : x.toNat < 2 ^ y.toNat) : bvlshr x y = literal n 0 := by
  apply toNat_injective
  rw [toNat_bvlshr, toNat_literal, Nat.zero_mod, Nat.div_eq_of_lt h]

theorem bvlshr_eq_zero_of_le (x y : _root_.BitVec n)
    (h : x.toNat ≤ y.toNat) : bvlshr x y = literal n 0 :=
  Learned.BitVec.bvlshr_eq_zero_of_lt x y (Nat.lt_of_le_of_lt h Nat.lt_two_pow_self)

/-- Bits below the shift amount cannot overlap the shifted word. -/
theorem bvand_bvshl_eq_zero_of_lt (x y z : _root_.BitVec n)
    (h : x.toNat < 2 ^ z.toNat) : bvand x (bvshl y z) = literal n 0 := by
  rw [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq']
  apply _root_.BitVec.eq_of_getElem_eq
  intro i hi
  by_cases hiz : i < z.toNat
  · simp [bvand, literal, _root_.BitVec.getElem_shiftLeft, hiz]
  · have hx : x[i] = false := by
      rw [_root_.BitVec.getElem_eq_testBit_toNat]
      apply SMT.Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hiz))
    simp [bvand, literal, hx]

/-- Disjoint low and shifted high bits add without carrying. -/
theorem bvor_bvshl_eq_bvadd_of_lt (x y z : _root_.BitVec n)
    (h : x.toNat < 2 ^ z.toNat) : bvor x (bvshl y z) = bvadd x (bvshl y z) := by
  apply _root_.BitVec.eq_of_toNat_eq
  simp only [bvor, bvadd, bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq',
    _root_.BitVec.toNat_or, _root_.BitVec.toNat_add, _root_.BitVec.toNat_shiftLeft]
  conv => lhs; lhs; rw [← Nat.mod_eq_of_lt x.isLt]
  rw [← SMT.Nat.or_mod_two_pow, SMT.Nat.or_comm,
    ← SMT.Nat.shiftLeft_add_eq_or_of_lt h, Nat.add_comm, Nat.add_mod_mod]

theorem bvand_bvshl_self (x y : _root_.BitVec n) :
    bvand x (bvshl y x) = literal n 0 :=
  Learned.BitVec.bvand_bvshl_eq_zero_of_lt x y x Nat.lt_two_pow_self

theorem bvor_bvshl_self (x y : _root_.BitVec n) :
    bvor x (bvshl y x) = bvadd x (bvshl y x) :=
  Learned.BitVec.bvor_bvshl_eq_bvadd_of_lt x y x Nat.lt_two_pow_self

theorem bvand_bvnot_of_bvand_eq_zero (x y : _root_.BitVec n)
    (h : bvand x y = literal n 0) : bvand x (bvnot y) = x := by
  apply _root_.BitVec.eq_of_getElem_eq
  intro i hi
  have hb := congrArg (fun a : _root_.BitVec n => a[i]) h
  simp only [bvand, bvnot, literal, _root_.BitVec.getElem_and,
    _root_.BitVec.getElem_not, _root_.BitVec.getElem_zero] at *
  cases hx : x[i] <;> cases hy : y[i] <;> simp_all

theorem bvor_bvnot_of_bvand_eq_zero (x y : _root_.BitVec n)
    (h : bvand x y = literal n 0) : bvor x (bvnot y) = bvnot y := by
  apply _root_.BitVec.eq_of_getElem_eq
  intro i hi
  have hb := congrArg (fun a : _root_.BitVec n => a[i]) h
  simp only [bvand, bvor, bvnot, literal, _root_.BitVec.getElem_and,
    _root_.BitVec.getElem_or, _root_.BitVec.getElem_not, _root_.BitVec.getElem_zero] at *
  cases hx : x[i] <;> cases hy : y[i] <;> simp_all

theorem bvshl_one (x : _root_.BitVec n) : bvshl x (literal n 1) = bvadd x x := by
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    have h : 1 < 2 ^ (n+1) := Nat.one_lt_two_pow (by omega)
    simp only [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq', literal,
      _root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, bvadd]
    rw [_root_.BitVec.shiftLeft_eq_mul_twoPow]
    have ht : _root_.BitVec.twoPow (n+1) 1 = 2#(n+1) := by
      apply _root_.BitVec.eq_of_toNat_eq
      simp only [_root_.BitVec.toNat_twoPow, _root_.BitVec.toNat_ofNat, Nat.pow_one]
    rw [ht, _root_.BitVec.mul_two]

theorem bvlshr_bvnot_of_eq_zero (x y : _root_.BitVec n)
    (h : bvlshr x y = literal n 0) :
    bvlshr (bvnot x) y = bvlshr (bvnot (literal n 0)) y := by
  rw [← Learned.BitVec.bvor_bvnot x, Learned.BitVec.bvlshr_bvor, h]
  simp [bvor, literal]

/-- Shifting left and back right keeps exactly the surviving low bits. -/
theorem bvlshr_bvshl_mask (x y : _root_.BitVec n) :
    bvlshr (bvshl x y) y = bvand x (bvlshr (bvnot (literal n 0)) y) := by
  apply _root_.BitVec.eq_of_getElem_eq
  intro i hi
  have hle : ¬ y.toNat + i < y.toNat := by omega
  simp [hle, ← _root_.BitVec.getLsbD_eq_getElem, bvshl_eq_shiftLeft,
    _root_.BitVec.shiftLeft_eq', bvlshr, _root_.BitVec.ushiftRight_eq',
    bvand, bvnot, literal, _root_.BitVec.getLsbD_shiftLeft, Bool.and_comm]

end Learned.BitVec
