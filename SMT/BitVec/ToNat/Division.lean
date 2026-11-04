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

public import SMT.BitVec.Semantics.Division
public import SMT.BitVec.ToNat.Conversion

@[expose] public section

namespace SMT.BitVec

/-- SMT division by zero returns the all-ones value, not Nat.div's zero. -/
theorem toNat_bvudiv (x y : _root_.BitVec n) :
    (bvudiv x y).toNat = if y.toNat = 0 then 2 ^ n - 1 else x.toNat / y.toNat := by
  simpa [← _root_.BitVec.toNat_inj] using bvudiv_semantics x y
theorem toNat_bvurem (x y : _root_.BitVec n) :
    (bvurem x y).toNat = x.toNat % y.toNat := rfl
/-- Signed division uses truncation, with SMT-specific zero-divisor behavior. -/
theorem toNat_bvsdiv (x y : _root_.BitVec n) :
    (bvsdiv x y).toNat =
      if y.toNat = 0 then
        if signedValue n x.toNat < 0 then 1 % 2 ^ n else 2 ^ n - 1
      else ((signedValue n x.toNat).tdiv (signedValue n y.toNat) % (2 ^ n : Nat)).toNat := by
  by_cases hy : y = literal n 0
  · subst y
    rw [bvsdiv_zero]
    have hz : signedValue n 0 = 0 := by simp [signedValue]
    by_cases hx : signedValue n x.toNat < 0 <;>
      simp [literal, bvslt, _root_.BitVec.slt, toInt_toNat, unsignedMax, hz, hx,
        Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos n) (by decide : 0 < (1 : Nat)))]
  · have hy' : y.toNat ≠ 0 := by simpa [← _root_.BitVec.toNat_inj] using hy
    simp only [hy', ↓reduceIte]
    rw [bvsdiv_semantics x y hy]
    exact toNat_int_to_bv _ _
theorem toNat_bvsrem (x y : _root_.BitVec n) :
    (bvsrem x y).toNat =
      ((signedValue n x.toNat).tmod (signedValue n y.toNat) % (2 ^ n : Nat)).toNat := by
  rw [toNat_of_toInt, _root_.BitVec.toInt_srem]
  rfl
theorem toNat_bvsmod (x y : _root_.BitVec n) :
    (bvsmod x y).toNat =
      ((signedValue n x.toNat).fmod (signedValue n y.toNat) % (2 ^ n : Nat)).toNat := by
  rw [toNat_of_toInt, _root_.BitVec.toInt_smod]
  rfl

end SMT.BitVec
