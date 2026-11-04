/-
Copyright (c) 2023-2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Adapted from Lean 4 v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52).
Upstream: Init/Data/BitVec/{Basic,Bootstrap,Lemmas,Bitblast}.lean.
SMT-facing statements and adaptations are documented in UPSTREAM.md and upstream.json.
-/
module
prelude

public import SMT.BitVec.Conversion
public import Init.Data.BitVec.Lemmas

@[expose] public section

namespace SMT.BitVec

/-- Signed interpretation expressed using only the unsigned representation and width. -/
abbrev signedValue (n u : Nat) : Int :=
  if 2 * u < 2 ^ n then (u : Int) else (u : Int) - (2 ^ n : Nat)
theorem toInt_toNat (x : _root_.BitVec n) : x.toInt = signedValue n x.toNat := rfl
theorem toNat_int_to_bv (n : Nat) (z : Int) :
    (int_to_bv n z).toNat = (z % (2 ^ n : Nat)).toNat := _root_.BitVec.toNat_ofInt z
theorem toNat_int_to_pbv (n : Nat) (z : Int) :
    (int_to_pbv n z).toNat = (z % (2 ^ n : Nat)).toNat := toNat_int_to_bv n z
theorem ubv_to_int_toNat (x : _root_.BitVec n) : ubv_to_int x = (x.toNat : Int) := rfl
theorem sbv_to_int_toNat (x : _root_.BitVec n) :
    sbv_to_int x = signedValue n x.toNat := rfl
/-- Recover an unsigned representation from a signed result (also handles width zero). -/
theorem toNat_of_toInt (x : _root_.BitVec n) :
    x.toNat = (x.toInt % (2 ^ n : Nat)).toNat := by
  calc
    x.toNat = (_root_.BitVec.ofInt n x.toInt).toNat :=
      congrArg _root_.BitVec.toNat (_root_.BitVec.ofInt_toInt (x := x)).symm
    _ = _ := _root_.BitVec.toNat_ofInt _

end SMT.BitVec
