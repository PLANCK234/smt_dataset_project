/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local derivations from Lean 4.34.1 Init and the SMT API.
Source dependencies and pinned revisions: upstream.json.
-/
module
prelude

public import Init.Data.BitVec.Bootstrap
public import LEMMAS_learned.Nat.Bitwise
public import SMT.BitVec.Rewrite.Arithmetic
public import SMT.BitVec.Rewrite.Bitwise

@[expose] public section

namespace Learned.BitVec
open SMT.BitVec

theorem bvadd_bvnot (x : _root_.BitVec n) :
    bvadd x (bvnot x) = bvnot (literal n 0) := by
  simp only [bvadd, bvnot, literal, _root_.BitVec.not_eq_neg_add, _root_.BitVec.neg_zero,
    _root_.BitVec.sub_eq_add_neg, ← _root_.BitVec.add_assoc, _root_.BitVec.add_right_neg]

theorem bvmul_bvnot_zero (x : _root_.BitVec n) :
    bvmul x (bvnot (literal n 0)) = bvneg x := by
  simp only [bvmul, bvnot, literal, bvneg, _root_.BitVec.not_zero,
    ← _root_.BitVec.neg_one_eq_allOnes, _root_.BitVec.mul_neg, _root_.BitVec.mul_one]

theorem bvadd_bvnot_zero (x : _root_.BitVec n) :
    bvadd x (bvnot (literal n 0)) = bvnot (bvneg x) := by
  simp only [bvadd, bvnot, literal, bvneg, _root_.BitVec.not_zero,
    ← _root_.BitVec.neg_one_eq_allOnes, _root_.BitVec.add_neg_eq_sub, _root_.BitVec.not_neg]

theorem bvneg_bvnot_zero : bvneg (bvnot (literal n 0)) = literal n 1 := by
  simp [bvneg, bvnot, literal, _root_.BitVec.not_zero, ← _root_.BitVec.neg_one_eq_allOnes]

theorem bvor_bvnot (x : _root_.BitVec n) :
    bvor x (bvnot x) = bvnot (literal n 0) := by
  apply _root_.BitVec.eq_of_getElem_eq
  intro i hi
  simp [bvor, bvnot, literal]

theorem bvand_bvor_absorb (x y : _root_.BitVec n) : bvand x (bvor x y) = x := by
  apply _root_.BitVec.eq_of_getElem_eq
  intro i hi
  simp only [bvand, bvor, _root_.BitVec.getElem_and, _root_.BitVec.getElem_or]
  cases x[i] <;> simp

theorem bvor_bvand_absorb (x y : _root_.BitVec n) : bvor x (bvand x y) = x := by
  apply _root_.BitVec.eq_of_getElem_eq
  intro i hi
  simp only [bvand, bvor, _root_.BitVec.getElem_and, _root_.BitVec.getElem_or]
  cases x[i] <;> simp

theorem bvor_bvnot_zero (x : _root_.BitVec n) : bvor x (bvnot (literal n 0)) = bvnot (literal n 0) := by
  simp [bvor, bvnot, literal]

theorem bvand_bvnot_zero (x : _root_.BitVec n) : bvand x (bvnot (literal n 0)) = x := by
  simp [bvand, bvnot, literal]

theorem bvor_eq_bvadd_of_bvand_eq_zero (x y : _root_.BitVec n)
    (h : bvand x y = literal n 0) : bvor x y = bvadd x y := by
  have hn : x.toNat &&& y.toNat = 0 := congrArg _root_.BitVec.toNat h
  apply _root_.BitVec.eq_of_toNat_eq
  simp only [bvor, bvadd, _root_.BitVec.toNat_or, _root_.BitVec.toNat_add]
  rw [← Learned.Nat.or_eq_add_of_and_eq_zero hn]
  exact (Nat.mod_eq_of_lt (_root_.BitVec.isLt (x ||| y))).symm

theorem toNat_bvadd_of_bvand_eq_zero (x y : _root_.BitVec n)
    (h : bvand x y = literal n 0) : (bvadd x y).toNat = x.toNat + y.toNat := by
  rw [← Learned.BitVec.bvor_eq_bvadd_of_bvand_eq_zero x y h]
  have hn : x.toNat &&& y.toNat = 0 := congrArg _root_.BitVec.toNat h
  exact Learned.Nat.or_eq_add_of_and_eq_zero hn

theorem bvand_bvand_eq_zero_of_right (x y z : _root_.BitVec n)
    (h : bvand x z = literal n 0) : bvand x (bvand y z) = literal n 0 := by
  rw [bvand_comm y z, ← bvand_assoc, h, bvand_comm, bvand_zero]

end Learned.BitVec
