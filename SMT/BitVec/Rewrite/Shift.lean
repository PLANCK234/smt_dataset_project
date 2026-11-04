/-
Copyright (c) 2023-2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Adapted from Lean v4.34.1, Init/Data/BitVec/Lemmas.lean.
Changes: statements use the SMT public API; proof dependencies remain in Init.
The exact upstream declarations are recorded in upstream.json.
-/
module
prelude
public import Init.Data.BitVec.Bootstrap

public import SMT.BitVec.Shift
public import Init.Data.BitVec.Lemmas
public import SMT.BitVec.Bitwise

@[expose] public section

namespace SMT.BitVec


theorem bvshl_zero (x : _root_.BitVec n) : bvshl x (literal n 0) = x := by
  rw [bvshl_eq_shiftLeft]; simp [literal]
theorem bvshl_large (x y : _root_.BitVec n) (h : n ≤ y.toNat) :
    bvshl x y = literal n 0 := by simp [bvshl, h, literal]
theorem bvlshr_zero (x : _root_.BitVec n) : bvlshr x (literal n 0) = x := by
  simp [bvlshr, literal]
theorem bvashr_zero (x : _root_.BitVec n) : bvashr x (literal n 0) = x := by
  simp [bvashr, literal]
theorem bvshl_bvand (x y z : _root_.BitVec n) :
    bvshl (bvand x y) z = bvand (bvshl x z) (bvshl y z) := by
  simp only [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq']
  exact _root_.BitVec.shiftLeft_and_distrib x y z.toNat
theorem bvshl_bvor (x y z : _root_.BitVec n) :
    bvshl (bvor x y) z = bvor (bvshl x z) (bvshl y z) := by
  simp only [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq']
  exact _root_.BitVec.shiftLeft_or_distrib x y z.toNat
theorem bvshl_bvxor (x y z : _root_.BitVec n) :
    bvshl (bvxor x y) z = bvxor (bvshl x z) (bvshl y z) := by
  simp only [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq']
  exact _root_.BitVec.shiftLeft_xor_distrib x y z.toNat

end SMT.BitVec
