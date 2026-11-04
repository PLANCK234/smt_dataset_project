/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local derivations from Lean 4.34.1 Init and the SMT API.
Source dependencies and pinned revisions: upstream.json.
-/
module
prelude

public import LEMMAS_learned.BitVec.Bitwise

@[expose] public section

namespace Learned.BitVec
open SMT.BitVec

theorem bvadd_bvand_bvnot (x y : _root_.BitVec n) :
    bvadd x (bvand y (bvnot x)) = bvor x y := by
  rw [← Learned.BitVec.bvor_eq_bvadd_of_bvand_eq_zero x _ (Learned.BitVec.bvand_bvand_eq_zero_of_right x y _ (bvand_bvnot x))]
  apply _root_.BitVec.eq_of_getElem_eq
  intro i hi
  simp only [bvor, bvand, bvnot, _root_.BitVec.getElem_or, _root_.BitVec.getElem_and,
    _root_.BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> rfl

theorem bvadd_bvand_parts (x y : _root_.BitVec n) :
    bvadd (bvand x y) (bvand x (bvnot y)) = x := by
  rw [← Learned.BitVec.bvor_eq_bvadd_of_bvand_eq_zero]
  · apply _root_.BitVec.eq_of_getElem_eq
    intro i hi
    simp only [bvor, bvand, bvnot, _root_.BitVec.getElem_or, _root_.BitVec.getElem_and,
      _root_.BitVec.getElem_not]
    cases x[i] <;> cases y[i] <;> rfl
  · apply _root_.BitVec.eq_of_getElem_eq
    intro i hi
    simp only [bvand, bvnot, literal, _root_.BitVec.getElem_and, _root_.BitVec.getElem_not]
    cases x[i] <;> cases y[i] <;> simp

theorem bvadd_bvneg_bvand (x y : _root_.BitVec n) :
    bvadd x (bvneg (bvand x y)) = bvand x (bvnot y) := by
  have h := Learned.BitVec.bvadd_bvand_parts x y
  change (x + -(bvand x y)) = _
  rw [_root_.BitVec.add_neg_eq_sub]
  apply _root_.BitVec.sub_eq_iff_eq_add.mpr
  change x = bvadd (bvand x (bvnot y)) (bvand x y)
  rw [bvadd_comm]
  exact h.symm

theorem bvadd_bvneg_bvor (x y : _root_.BitVec n) :
    bvadd x (bvneg (bvor x y)) = bvneg (bvand (bvnot x) y) := by
  rw [← Learned.BitVec.bvadd_bvand_bvnot]
  simp only [bvadd, bvneg, _root_.BitVec.neg_add, _root_.BitVec.sub_eq_add_neg,
    ← _root_.BitVec.add_assoc, _root_.BitVec.add_right_neg, _root_.BitVec.zero_add]
  rw [bvand_comm]

theorem bvadd_bvand_bvor (x y : _root_.BitVec n) :
    bvadd (bvand x y) (bvor x y) = bvadd x y := by
  rw [← Learned.BitVec.bvadd_bvand_bvnot x y]
  rw [bvadd_comm (bvand x y), bvadd_assoc, bvand_comm x y,
    bvadd_comm (bvand y (bvnot x)), Learned.BitVec.bvadd_bvand_parts]

theorem bvneg_bvand_bvneg (x : _root_.BitVec n) :
    bvneg (bvand x (bvneg x)) = bvor x (bvneg x) := by
  have h := Learned.BitVec.bvadd_bvand_bvor x (bvneg x)
  rw [bvadd_bvneg] at h
  apply (_root_.BitVec.add_right_inj (bvand x (bvneg x))).mp
  exact (_root_.BitVec.add_right_neg _).trans h.symm

/-- Source: BitVec.mul_neg; expressed using the local SMT API. -/
theorem bvmul_bvneg (x y : _root_.BitVec n) :
    bvmul x (bvneg y) = bvneg (bvmul x y) :=
  _root_.BitVec.mul_neg x y

end Learned.BitVec
