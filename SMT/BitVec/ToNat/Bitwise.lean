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
public import Init.Data.BitVec.Bootstrap

public import SMT.BitVec.Bitwise
public import Init.Data.BitVec.Lemmas

@[expose] public section

namespace SMT.BitVec

theorem toNat_bvnot (x : _root_.BitVec n) :
    (bvnot x).toNat = 2 ^ n - 1 - x.toNat := _root_.BitVec.toNat_not
theorem toNat_bvand (x y : _root_.BitVec n) :
    (bvand x y).toNat = x.toNat &&& y.toNat := rfl
theorem toNat_bvor (x y : _root_.BitVec n) :
    (bvor x y).toNat = x.toNat ||| y.toNat := rfl
theorem toNat_bvxor (x y : _root_.BitVec n) :
    (bvxor x y).toNat = x.toNat ^^^ y.toNat := rfl
theorem toNat_bvnand (x y : _root_.BitVec n) :
    (bvnand x y).toNat = 2 ^ n - 1 - (x.toNat &&& y.toNat) := toNat_bvnot (bvand x y)
theorem toNat_bvnor (x y : _root_.BitVec n) :
    (bvnor x y).toNat = 2 ^ n - 1 - (x.toNat ||| y.toNat) := toNat_bvnot (bvor x y)
theorem toNat_bvxnor (x y : _root_.BitVec n) :
    (bvxnor x y).toNat = 2 ^ n - 1 - (x.toNat ^^^ y.toNat) := toNat_bvnot (bvxor x y)
theorem toNat_bvcomp (x y : _root_.BitVec n) :
    (bvcomp x y).toNat = if x.toNat = y.toNat then 1 else 0 := by
  by_cases h : x = y <;> simp [bvcomp, _root_.BitVec.toNat_inj, h]

end SMT.BitVec
