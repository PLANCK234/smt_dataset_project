/-
Copyright (c) 2023-2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Adapted from Lean v4.34.1, Init/Data/BitVec/Lemmas.lean.
Changes: statements use the SMT public API; proof dependencies remain in Init.
The exact upstream declarations are recorded in upstream.json.
-/
module
prelude

public import SMT.BitVec.Arithmetic
public import Init.Data.BitVec.Lemmas

@[expose] public section

namespace SMT.BitVec

/-- Source: BitVec.add_comm. Use with rw; deliberately not a simp rule. -/
theorem bvadd_comm (x y : _root_.BitVec n) : bvadd x y = bvadd y x :=
  _root_.BitVec.add_comm x y
/-- Source: BitVec.add_assoc. -/
theorem bvadd_assoc (x y z : _root_.BitVec n) :
    bvadd (bvadd x y) z = bvadd x (bvadd y z) := _root_.BitVec.add_assoc x y z
/-- Source: BitVec.mul_comm. Use with rw; deliberately not a simp rule. -/
theorem bvmul_comm (x y : _root_.BitVec n) : bvmul x y = bvmul y x :=
  _root_.BitVec.mul_comm x y
/-- Source: BitVec.mul_assoc. -/
theorem bvmul_assoc (x y z : _root_.BitVec n) :
    bvmul (bvmul x y) z = bvmul x (bvmul y z) := _root_.BitVec.mul_assoc x y z
theorem bvadd_zero (x : _root_.BitVec n) : bvadd x (literal n 0) = x := by
  simp [bvadd, literal]
theorem zero_bvadd (x : _root_.BitVec n) : bvadd (literal n 0) x = x := by
  simp [bvadd, literal]
theorem bvmul_zero (x : _root_.BitVec n) : bvmul x (literal n 0) = literal n 0 := by
  simp [bvmul, literal]
theorem zero_bvmul (x : _root_.BitVec n) : bvmul (literal n 0) x = literal n 0 := by
  simp [bvmul, literal]
theorem bvmul_one (x : _root_.BitVec n) : bvmul x (literal n 1) = x := by
  simp [bvmul, literal]
theorem one_bvmul (x : _root_.BitVec n) : bvmul (literal n 1) x = x := by
  simp [bvmul, literal]
theorem bvsub_zero (x : _root_.BitVec n) : bvsub x (literal n 0) = x := by
  simp [bvsub, literal]
theorem bvsub_self (x : _root_.BitVec n) : bvsub x x = literal n 0 := by
  simp [bvsub, literal]
theorem bvneg_bvneg (x : _root_.BitVec n) : bvneg (bvneg x) = x := by
  simp [bvneg]
theorem bvadd_bvneg (x : _root_.BitVec n) : bvadd x (bvneg x) = literal n 0 := by
  simp [bvadd, bvneg, literal, _root_.BitVec.add_neg_eq_sub]

theorem bvsub_eq_bvadd_bvneg (x y : _root_.BitVec n) : bvsub x y = bvadd x (bvneg y) :=
  _root_.BitVec.sub_eq_add_neg x y
theorem bvadd_bvsub_cancel (x y : _root_.BitVec n) : bvsub (bvadd x y) y = x := by
  exact _root_.BitVec.add_sub_cancel x y
theorem bvmul_bvadd (x y z : _root_.BitVec n) :
    bvmul x (bvadd y z) = bvadd (bvmul x y) (bvmul x z) := _root_.BitVec.mul_add
theorem bvadd_bvmul (x y z : _root_.BitVec n) :
    bvmul (bvadd x y) z = bvadd (bvmul x z) (bvmul y z) := _root_.BitVec.add_mul

end SMT.BitVec
