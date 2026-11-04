/-
Copyright (c) 2023-2024 Lean FRO, LLC. All rights reserved.
Copyright (c) 2020 Simon Hudon. Mathlib authors: Simon Hudon, Harun Khan, Alex Keizer.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Adapted from Lean 4 v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52).
Upstream: Init/Data/BitVec/{Basic,Bootstrap,Lemmas,Bitblast}.lean.
SMT-facing statements and adaptations are documented in UPSTREAM.md and upstream.json.
-/
module
prelude

public import Init.Data.Nat.Div.Lemmas

public import Init.RCases
public import Init.Data.Nat.Mod

public import SMT.BitVec.Basic
public import Init.Data.BitVec.Bootstrap

@[expose] public section

namespace SMT.BitVec

/-- Source: Mathlib.Data.BitVec.toNat_injective; proof extracted without Function.Injective. -/
theorem toNat_injective {x y : _root_.BitVec n} (h : x.toNat = y.toNat) : x = y := by
  rcases x with ⟨⟨a, ha⟩⟩
  rcases y with ⟨⟨b, hb⟩⟩
  change a = b at h
  subst b
  rfl
/-- Source: Mathlib.Data.BitVec.toFin_injective; no Mathlib typeclass dependencies. -/
theorem toFin_injective {x y : _root_.BitVec n} (h : x.toFin = y.toFin) : x = y := by
  cases x; cases y; cases h; rfl

theorem eq_iff_toNat_eq (x y : _root_.BitVec n) : x = y ↔ x.toNat = y.toNat :=
  ⟨fun h => congrArg _ h, toNat_injective⟩
theorem toNat_lt (x : _root_.BitVec n) : x.toNat < 2 ^ n := x.isLt
theorem toNat_literal (n v : Nat) : (literal n v).toNat = v % 2 ^ n := rfl
theorem toNat_literal_of_lt (n v : Nat) (h : v < 2 ^ n) :
    (literal n v).toNat = v := Nat.mod_eq_of_lt h
theorem toNat_mod (x : _root_.BitVec n) : x.toNat % 2 ^ n = x.toNat :=
  Nat.mod_eq_of_lt x.isLt
theorem literal_toNat (x : _root_.BitVec n) : literal n x.toNat = x := by
  apply toNat_injective
  exact toNat_mod x

end SMT.BitVec
