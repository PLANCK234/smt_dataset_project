/-
Copyright (c) 2023-2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Adapted from Lean 4 v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52).
Upstream: Init/Data/BitVec/{Basic,Bootstrap,Lemmas,Bitblast}.lean.
SMT-facing statements and adaptations are documented in UPSTREAM.md and upstream.json.
-/
module
prelude

public import Init.ByCases
public import SMT.BitVec.Semantics.Structure

@[expose] public section

namespace SMT.BitVec

theorem toNat_concat (x : _root_.BitVec m) (y : _root_.BitVec n) :
    (concat x y).toNat = x.toNat * 2 ^ n + y.toNat := concat_semantics x y
/-- This total Lean equation holds even outside the checked SMT extraction domain. -/
theorem toNat_extract (hi lo : Nat) (x : _root_.BitVec n) :
    (extract hi lo x).toNat = (x.toNat / 2 ^ lo) % 2 ^ (hi - lo + 1) := by
  simp [extract, Nat.shiftRight_eq_div_pow]
theorem toNat_zeroExtend (extra : Nat) (x : _root_.BitVec n) :
    (zeroExtend extra x).toNat = x.toNat := zeroExtend_semantics extra x
theorem toNat_signExtend (extra : Nat) (x : _root_.BitVec n) :
    (signExtend extra x).toNat = x.toNat +
      if 2 * x.toNat < 2 ^ n then 0 else 2 ^ (n + extra) - 2 ^ n := by
  rw [_root_.BitVec.toNat_signExtend, _root_.BitVec.toNat_setWidth_of_le (Nat.le_add_right _ _)]
  by_cases h : x.msb = false
  · have hx := (_root_.BitVec.msb_eq_false_iff_two_mul_lt).mp h
    simp [h, hx]
  · have hx : ¬ 2 * x.toNat < 2 ^ n := by
      simpa only [← _root_.BitVec.msb_eq_false_iff_two_mul_lt] using h
    simp [h, hx]
theorem toNat_rotateLeft (count : Nat) (x : _root_.BitVec n) :
    (rotateLeft count x).toNat =
      (x.toNat * 2 ^ (count % n)) % 2 ^ n ||| x.toNat / 2 ^ (n - count % n) := by
  rw [_root_.BitVec.toNat_rotateLeft]
  simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
theorem toNat_rotateRight (count : Nat) (x : _root_.BitVec n) :
    (rotateRight count x).toNat =
      x.toNat / 2 ^ (count % n) ||| (x.toNat * 2 ^ (n - count % n)) % 2 ^ n := by
  rw [_root_.BitVec.toNat_rotateRight]
  simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
/-- Finite geometric repetition, avoiding division and its width-zero corner. -/
def repeatValue (width value : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => value * 2 ^ (width * count) + repeatValue width value count

theorem toNat_repeat (count : Nat) (x : _root_.BitVec n) :
    (SMT.BitVec.repeat count x).toNat = repeatValue n x.toNat count := by
  induction count with
  | zero => rfl
  | succ k ih =>
    simp only [SMT.BitVec.repeat, _root_.BitVec.replicate, _root_.BitVec.toNat_cast,
      _root_.BitVec.toNat_append, repeatValue]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (x.replicate k).isLt, Nat.shiftLeft_eq]
    exact congrArg (fun v => x.toNat * 2 ^ (n * k) + v) ih


theorem toNat_pextract (hi lo : Nat) (x : _root_.BitVec n) :
    (pextract hi lo x).toNat = (x.toNat / 2 ^ lo) % 2 ^ (hi - lo + 1) := toNat_extract hi lo x
theorem toNat_pzero_extend (extra : Nat) (x : _root_.BitVec n) :
    (pzero_extend extra x).toNat = x.toNat := toNat_zeroExtend extra x
theorem toNat_psign_extend (extra : Nat) (x : _root_.BitVec n) :
    (psign_extend extra x).toNat = x.toNat +
      if 2 * x.toNat < 2 ^ n then 0 else 2 ^ (n + extra) - 2 ^ n := toNat_signExtend extra x

end SMT.BitVec
