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

public import SMT.BitVec.Semantics.Shift
public import SMT.BitVec.ToNat.Conversion

@[expose] public section

namespace SMT.BitVec

theorem toNat_bvshl (x y : _root_.BitVec n) :
    (bvshl x y).toNat = (x.toNat * 2 ^ y.toNat) % 2 ^ n := bvshl_semantics x y
theorem toNat_bvlshr (x y : _root_.BitVec n) :
    (bvlshr x y).toNat = x.toNat / 2 ^ y.toNat := bvlshr_semantics x y
/-- Arithmetic shift: sign is read from the unsigned value; no unbounded complement. -/
theorem toNat_bvashr (x y : _root_.BitVec n) :
    (bvashr x y).toNat =
      if 2 * x.toNat < 2 ^ n then x.toNat / 2 ^ y.toNat
      else 2 ^ n - 1 - (2 ^ n - 1 - x.toNat) / 2 ^ y.toNat := by
  rw [_root_.BitVec.toNat_sshiftRight']
  by_cases h : x.msb = false
  · have hx := (_root_.BitVec.msb_eq_false_iff_two_mul_lt).mp h
    simp [h, hx, Nat.shiftRight_eq_div_pow]
  · have hx : ¬ 2 * x.toNat < 2 ^ n := by
      simpa only [← _root_.BitVec.msb_eq_false_iff_two_mul_lt] using h
    simp [h, hx, Nat.shiftRight_eq_div_pow]

end SMT.BitVec
