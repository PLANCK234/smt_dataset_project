/-
Copyright (c) 2023-2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Adapted from Lean 4 v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52).
Upstream: Init/Data/BitVec/{Basic,Bootstrap,Lemmas,Bitblast}.lean.
SMT-facing statements and adaptations are documented in UPSTREAM.md and upstream.json.
-/
module
prelude

public import SMT.BitVec.Semantics.Overflow
public import SMT.BitVec.ToNat.Conversion

@[expose] public section

namespace SMT.BitVec

theorem bvuaddo_toNat (x y : _root_.BitVec n) :
    bvuaddo x y = decide (x.toNat + y.toNat ≥ 2 ^ n) := rfl
theorem bvusubo_toNat (x y : _root_.BitVec n) :
    bvusubo x y = decide (x.toNat < y.toNat) := rfl
theorem bvumulo_toNat (x y : _root_.BitVec n) :
    bvumulo x y = decide (x.toNat * y.toNat ≥ 2 ^ n) := rfl

theorem bvnego_toNat (x : _root_.BitVec n) :
    bvnego x = true ↔ signedValue n x.toNat = signedMin n := bvnego_semantics x
theorem bvsaddo_toNat (x y : _root_.BitVec n) :
    bvsaddo x y = true ↔
      signedValue n x.toNat + signedValue n y.toNat < signedMin n ∨
      signedMax n < signedValue n x.toNat + signedValue n y.toNat := bvsaddo_semantics x y
theorem bvssubo_toNat (x y : _root_.BitVec n) :
    bvssubo x y = true ↔
      signedValue n x.toNat - signedValue n y.toNat < signedMin n ∨
      signedMax n < signedValue n x.toNat - signedValue n y.toNat := bvssubo_semantics x y
theorem bvsmulo_toNat (x y : _root_.BitVec n) :
    bvsmulo x y = true ↔
      signedValue n x.toNat * signedValue n y.toNat < signedMin n ∨
      signedMax n < signedValue n x.toNat * signedValue n y.toNat := bvsmulo_semantics x y
theorem bvsdivo_toNat (hn : 0 < n) (x y : _root_.BitVec n) :
    bvsdivo x y = true ↔
      signedValue n x.toNat = signedMin n ∧ signedValue n y.toNat = -1 := bvsdivo_semantics hn x y

end SMT.BitVec
