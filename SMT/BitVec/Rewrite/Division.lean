/-
Copyright (c) 2023-2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Adapted from Lean v4.34.1, Init/Data/BitVec/Lemmas.lean.
Changes: statements use the SMT public API; proof dependencies remain in Init.
The exact upstream declarations are recorded in upstream.json.
-/
module
prelude
public import Init.Data.Int.DivMod.Lemmas

public import SMT.BitVec.Division
public import Init.Data.BitVec.Lemmas
public import SMT.BitVec.Semantics.Division
public import SMT.BitVec.ToNat.Division

@[expose] public section

namespace SMT.BitVec

theorem bvudiv_one (x : _root_.BitVec n) : bvudiv x (literal n 1) = x := by
  cases n with
  | zero => exact _root_.BitVec.of_length_zero.trans (_root_.BitVec.of_length_zero (x := x)).symm
  | succ k =>
    apply _root_.BitVec.eq_of_toNat_eq
    simp [toNat_bvudiv, literal]
theorem bvurem_one (x : _root_.BitVec n) : bvurem x (literal n 1) = literal n 0 := by
  simp [bvurem, literal]
theorem bvurem_self (x : _root_.BitVec n) : bvurem x (x) = literal n 0 := by
  simp [bvurem, literal]
theorem bvsrem_self (x : _root_.BitVec n) : bvsrem x (x) = literal n 0 := by
  simp [bvsrem, literal]
theorem bvsmod_self (x : _root_.BitVec n) : bvsmod x (x) = literal n 0 := by
  apply _root_.BitVec.eq_of_toInt_eq
  simp [bvsmod, literal, _root_.BitVec.toInt_smod]

end SMT.BitVec
