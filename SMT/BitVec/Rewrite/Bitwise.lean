/-
Copyright (c) 2023-2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Adapted from Lean v4.34.1, Init/Data/BitVec/Lemmas.lean.
Changes: statements use the SMT public API; proof dependencies remain in Init.
The exact upstream declarations are recorded in upstream.json.
-/
module
prelude

public import SMT.BitVec.Bitwise
public import Init.Data.BitVec.Lemmas

@[expose] public section

namespace SMT.BitVec

theorem bvand_comm (x y : _root_.BitVec n) : bvand x y = bvand y x :=
  _root_.BitVec.and_comm x y
theorem bvand_assoc (x y z : _root_.BitVec n) :
    bvand (bvand x y) z = bvand x (bvand y z) := _root_.BitVec.and_assoc x y z
theorem bvor_comm (x y : _root_.BitVec n) : bvor x y = bvor y x :=
  _root_.BitVec.or_comm x y
theorem bvor_assoc (x y z : _root_.BitVec n) :
    bvor (bvor x y) z = bvor x (bvor y z) := _root_.BitVec.or_assoc x y z
theorem bvxor_comm (x y : _root_.BitVec n) : bvxor x y = bvxor y x :=
  _root_.BitVec.xor_comm x y
theorem bvxor_assoc (x y z : _root_.BitVec n) :
    bvxor (bvxor x y) z = bvxor x (bvxor y z) := _root_.BitVec.xor_assoc x y z
theorem bvand_self (x : _root_.BitVec n) : bvand x x = x := by
  simp [bvand]
theorem bvor_self (x : _root_.BitVec n) : bvor x x = x := by
  simp [bvor]
theorem bvxor_self (x : _root_.BitVec n) : bvxor x x = literal n 0 := by
  simp [bvxor, literal]
theorem bvand_zero (x : _root_.BitVec n) : bvand x (literal n 0) = literal n 0 := by
  simp [bvand, literal]
theorem bvor_zero (x : _root_.BitVec n) : bvor x (literal n 0) = x := by
  simp [bvor, literal]
theorem bvxor_zero (x : _root_.BitVec n) : bvxor x (literal n 0) = x := by
  simp [bvxor, literal]
theorem bvnot_bvnot (x : _root_.BitVec n) : bvnot (bvnot x) = x := by
  simp [bvnot]
theorem bvand_bvnot (x : _root_.BitVec n) : bvand x (bvnot x) = literal n 0 := by
  simp [bvand, bvnot, literal]

theorem bvnot_bvand (x y : _root_.BitVec n) : bvnot (bvand x y) = bvor (bvnot x) (bvnot y) :=
  _root_.BitVec.not_and
theorem bvnot_bvor (x y : _root_.BitVec n) : bvnot (bvor x y) = bvand (bvnot x) (bvnot y) :=
  _root_.BitVec.not_or
theorem bvand_bvor (x y z : _root_.BitVec n) :
    bvand x (bvor y z) = bvor (bvand x y) (bvand x z) := _root_.BitVec.and_or_distrib_left
theorem bvnand_eq (x y : _root_.BitVec n) : bvnand x y = bvnot (bvand x y) := rfl
theorem bvnor_eq (x y : _root_.BitVec n) : bvnor x y = bvnot (bvor x y) := rfl
theorem bvxnor_eq (x y : _root_.BitVec n) : bvxnor x y = bvnot (bvxor x y) := rfl
theorem bvcomp_self (x : _root_.BitVec n) : bvcomp x x = literal 1 1 := by simp [bvcomp, literal]

end SMT.BitVec
