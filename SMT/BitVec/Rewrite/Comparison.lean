/-
Copyright (c) 2023-2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Adapted from Lean v4.34.1, Init/Data/BitVec/Lemmas.lean.
Changes: statements use the SMT public API; proof dependencies remain in Init.
The exact upstream declarations are recorded in upstream.json.
-/
module
prelude

public import Init.Data.Int.Order

public import SMT.BitVec.Comparison
public import Init.Data.BitVec.Lemmas

@[expose] public section

namespace SMT.BitVec

theorem bvult_self (x : _root_.BitVec n) : bvult x x = false := by
  simp [bvult, _root_.BitVec.ult]
theorem bvugt_self (x : _root_.BitVec n) : bvugt x x = false := by
  simp [bvugt, _root_.BitVec.ult]
theorem bvslt_self (x : _root_.BitVec n) : bvslt x x = false := by
  simp [bvslt, _root_.BitVec.slt]
theorem bvsgt_self (x : _root_.BitVec n) : bvsgt x x = false := by
  simp [bvsgt, _root_.BitVec.slt]
theorem bvule_self (x : _root_.BitVec n) : bvule x x = true := by
  simp [bvule, _root_.BitVec.ule]
theorem bvuge_self (x : _root_.BitVec n) : bvuge x x = true := by
  simp [bvuge, _root_.BitVec.ule]
theorem bvsle_self (x : _root_.BitVec n) : bvsle x x = true := by
  simp [bvsle, _root_.BitVec.sle]
theorem bvsge_self (x : _root_.BitVec n) : bvsge x x = true := by
  simp [bvsge, _root_.BitVec.sle]
theorem bvugt_eq (x y : _root_.BitVec n) : bvugt x y = bvult y x := rfl
theorem bvuge_eq (x y : _root_.BitVec n) : bvuge x y = bvule y x := rfl
theorem bvsgt_eq (x y : _root_.BitVec n) : bvsgt x y = bvslt y x := rfl
theorem bvsge_eq (x y : _root_.BitVec n) : bvsge x y = bvsle y x := rfl

end SMT.BitVec
