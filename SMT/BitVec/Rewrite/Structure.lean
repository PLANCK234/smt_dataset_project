/-
Copyright (c) 2023-2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Adapted from Lean v4.34.1, Init/Data/BitVec/Lemmas.lean.
Changes: statements use the SMT public API; proof dependencies remain in Init.
The exact upstream declarations are recorded in upstream.json.
-/
module
prelude

public import SMT.BitVec.Structure
public import Init.Data.BitVec.Lemmas
public import SMT.BitVec.Bitwise
public import SMT.BitVec.Semantics.Structure

@[expose] public section

namespace SMT.BitVec


theorem zeroExtend_zero (x : _root_.BitVec n) : zeroExtend 0 x = x := by simp [zeroExtend]
theorem signExtend_zero (x : _root_.BitVec n) : signExtend 0 x = x := by simp [signExtend]
theorem pzero_extend_zero (x : _root_.BitVec n) : pzero_extend 0 x = x := zeroExtend_zero x
theorem psign_extend_zero (x : _root_.BitVec n) : psign_extend 0 x = x := signExtend_zero x
theorem zeroExtend_bvand (extra : Nat) (x y : _root_.BitVec n) :
    zeroExtend extra (bvand x y) = bvand (zeroExtend extra x) (zeroExtend extra y) :=
  _root_.BitVec.setWidth_and
theorem signExtend_bvand (extra : Nat) (x y : _root_.BitVec n) :
    signExtend extra (bvand x y) = bvand (signExtend extra x) (signExtend extra y) :=
  _root_.BitVec.signExtend_and
theorem zeroExtend_bvor (extra : Nat) (x y : _root_.BitVec n) :
    zeroExtend extra (bvor x y) = bvor (zeroExtend extra x) (zeroExtend extra y) :=
  _root_.BitVec.setWidth_or
theorem signExtend_bvor (extra : Nat) (x y : _root_.BitVec n) :
    signExtend extra (bvor x y) = bvor (signExtend extra x) (signExtend extra y) :=
  _root_.BitVec.signExtend_or
theorem zeroExtend_bvxor (extra : Nat) (x y : _root_.BitVec n) :
    zeroExtend extra (bvxor x y) = bvxor (zeroExtend extra x) (zeroExtend extra y) :=
  _root_.BitVec.setWidth_xor
theorem signExtend_bvxor (extra : Nat) (x y : _root_.BitVec n) :
    signExtend extra (bvxor x y) = bvxor (signExtend extra x) (signExtend extra y) :=
  _root_.BitVec.signExtend_xor

end SMT.BitVec
