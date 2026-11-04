/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Author: Joe Hendrix.
Extracted from Lean v4.34.1, Init/Data/Nat/Bitwise/Lemmas.lean:31-86.
Changes: split modules; namespace Nat → SMT.Nat; cross-module helpers made public.
Original theorem names are retained; local simp registration and qualified names
are adapted at module boundaries. See UPSTREAM.md.
-/
module
prelude

public import Init.Data.Bool
public import Init.BinderPredicates

public import Init.ByCases
public import Init.Omega
public import Init.RCases
public import Init.TacticsExtra

import all Init.Data.Nat.Bitwise.Basic
public import Init.Data.Nat.Log2
public import Init.Data.Int.Pow
public import Init.Data.Nat.Lemmas

public section

namespace SMT.Nat
open _root_.Nat

theorem two_pow_succ_sub_succ_div_two : (2 ^ (n+1) - (x + 1)) / 2 = 2^n - (x/2 + 1) := by
  omega

theorem two_pow_succ_sub_one_div_two : (2 ^ (n+1) - 1) / 2 = 2^n - 1 :=
  two_pow_succ_sub_succ_div_two

theorem two_mul_sub_one {n : Nat} (n_pos : n > 0) : (2*n - 1) % 2 = 1 := by
  omega

/-! ### Preliminaries -/

/--
An induction principle for the natural numbers with two cases:
 * `n = 0`, and the motive is satisfied for `0`
 * `n > 0`, and the motive should be satisfied for `n` on the assumption that it is satisfied for
   `n / 2`.
-/
noncomputable def div2Induction {motive : Nat → Sort u}
    (n : Nat) (ind : ∀(n : Nat), (n > 0 → motive (n/2)) → motive n) : motive n := by
  induction n using Nat.strongRecOn with
  | ind n hyp =>
    apply ind
    intro n_pos
    if n_eq : n = 0 then
      simp [n_eq] at n_pos
    else
      apply hyp
      exact Nat.div_lt_self n_pos (Nat.le_refl _)

@[simp, grind =] theorem zero_and (x : Nat) : 0 &&& x = 0 := by
  simp only [HAnd.hAnd, AndOp.and, land]
  unfold bitwise
  simp

@[simp, grind =] theorem and_zero (x : Nat) : x &&& 0 = 0 := by
  simp only [HAnd.hAnd, AndOp.and, land]
  unfold bitwise
  simp

@[simp, grind =] theorem one_and_eq_mod_two (n : Nat) : 1 &&& n = n % 2 := by
  if n0 : n = 0 then
    subst n0; decide
  else
    simp only [HAnd.hAnd, AndOp.and, land]
    cases mod_two_eq_zero_or_one n with | _ h => simp [bitwise, n0, h]

@[simp, grind =] theorem and_one_is_mod (x : Nat) : x &&& 1 = x % 2 := by
  if xz : x = 0 then
    simp [xz]
  else
    have andz := and_zero (x/2)
    simp only [HAnd.hAnd, AndOp.and, land] at andz
    simp only [HAnd.hAnd, AndOp.and, land]
    unfold bitwise
    cases mod_two_eq_zero_or_one x with | _ p => simp [xz, p, andz]


end SMT.Nat
