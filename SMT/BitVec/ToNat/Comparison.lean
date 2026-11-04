/-
Copyright (c) 2023-2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Adapted from Lean 4 v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52).
Upstream: Init/Data/BitVec/{Basic,Bootstrap,Lemmas,Bitblast}.lean.
SMT-facing statements and adaptations are documented in UPSTREAM.md and upstream.json.
-/
module
prelude

public import SMT.BitVec.Comparison
public import SMT.BitVec.ToNat.Conversion

@[expose] public section

namespace SMT.BitVec

theorem bvult_toNat (x y : _root_.BitVec n) :
    bvult x y = decide (x.toNat < y.toNat) := rfl
theorem bvule_toNat (x y : _root_.BitVec n) :
    bvule x y = decide (x.toNat ≤ y.toNat) := rfl
theorem bvugt_toNat (x y : _root_.BitVec n) :
    bvugt x y = decide (y.toNat < x.toNat) := rfl
theorem bvuge_toNat (x y : _root_.BitVec n) :
    bvuge x y = decide (y.toNat ≤ x.toNat) := rfl
theorem bvslt_toNat (x y : _root_.BitVec n) :
    bvslt x y = decide (signedValue n x.toNat < signedValue n y.toNat) := rfl
theorem bvsle_toNat (x y : _root_.BitVec n) :
    bvsle x y = decide (signedValue n x.toNat ≤ signedValue n y.toNat) := rfl
theorem bvsgt_toNat (x y : _root_.BitVec n) :
    bvsgt x y = decide (signedValue n y.toNat < signedValue n x.toNat) := rfl
theorem bvsge_toNat (x y : _root_.BitVec n) :
    bvsge x y = decide (signedValue n y.toNat ≤ signedValue n x.toNat) := rfl

end SMT.BitVec
