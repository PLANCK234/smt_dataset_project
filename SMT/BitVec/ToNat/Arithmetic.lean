/-
Copyright (c) 2023-2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Adapted from Lean 4 v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52).
Upstream: Init/Data/BitVec/{Basic,Bootstrap,Lemmas,Bitblast}.lean.
SMT-facing statements and adaptations are documented in UPSTREAM.md and upstream.json.
-/
module
prelude

public import SMT.BitVec.Arithmetic
public import SMT.BitVec.ToNat.Basic

@[expose] public section

namespace SMT.BitVec

theorem toNat_bvneg (x : _root_.BitVec n) :
    (bvneg x).toNat = (2 ^ n - x.toNat) % 2 ^ n := _root_.BitVec.toNat_neg x
theorem toNat_bvadd (x y : _root_.BitVec n) :
    (bvadd x y).toNat = (x.toNat + y.toNat) % 2 ^ n := rfl
theorem toNat_bvsub (x y : _root_.BitVec n) :
    (bvsub x y).toNat = ((2 ^ n - y.toNat) + x.toNat) % 2 ^ n := rfl
theorem toNat_bvmul (x y : _root_.BitVec n) :
    (bvmul x y).toNat = (x.toNat * y.toNat) % 2 ^ n := rfl

theorem toNat_bvadd_of_lt (x y : _root_.BitVec n) (h : x.toNat + y.toNat < 2 ^ n) :
    (bvadd x y).toNat = x.toNat + y.toNat := Nat.mod_eq_of_lt h
theorem toNat_bvmul_of_lt (x y : _root_.BitVec n) (h : x.toNat * y.toNat < 2 ^ n) :
    (bvmul x y).toNat = x.toNat * y.toNat := Nat.mod_eq_of_lt h

end SMT.BitVec
