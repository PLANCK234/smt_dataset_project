/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Author: Joe Hendrix.
Extracted from Lean v4.34.1, Init/Data/Nat/Bitwise/Lemmas.lean:866-893.
Changes: split modules; namespace Nat → SMT.Nat; cross-module helpers made public.
Original theorem names are retained; local simp registration and qualified names
are adapted at module boundaries. See UPSTREAM.md.
-/
module
prelude

import all Init.Data.Nat.Bitwise.Basic
public import SMT.Nat.Shift

public section

namespace SMT.Nat
open _root_.Nat
attribute [local simp] testBit_add_one

/-! ### le -/

theorem le_of_testBit {n m : Nat} (h : ∀ i, n.testBit i = true → m.testBit i = true) : n ≤ m := by
  induction n using div2Induction generalizing m with | _ n ih
  have : n / 2 ≤ m / 2 := by
    rcases n with (_|n)
    · simp
    · exact ih (Nat.succ_pos _) fun i => by simpa using h (i + 1)
  rw [← div_add_mod n 2, ← div_add_mod m 2]
  cases hn : n.testBit 0
  · have hn2 : n % 2 = 0 := by simp at hn; omega
    rw [hn2]
    omega
  · have hn2 : n % 2 = 1 := by simpa using hn
    have hm2 : m % 2 = 1 := by simpa using h _ hn
    omega

theorem and_le_left {n m : Nat} : n &&& m ≤ n :=
  le_of_testBit (by simpa using fun i x _ => x)

theorem and_le_right {n m : Nat} : n &&& m ≤ m :=
  le_of_testBit (by simp)

theorem left_le_or {n m : Nat} : n ≤ n ||| m :=
  le_of_testBit (by simp [imp_or_left_iff_true])

theorem right_le_or {n m : Nat} : m ≤ n ||| m :=
  le_of_testBit (by simp [imp_or_right_iff_true])

end SMT.Nat
