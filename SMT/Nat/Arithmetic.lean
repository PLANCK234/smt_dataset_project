/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Author: Joe Hendrix.
Extracted from Lean v4.34.1, Init/Data/Nat/Bitwise/Lemmas.lean:712-775.
Changes: split modules; namespace Nat → SMT.Nat; cross-module helpers made public.
Original theorem names are retained; local simp registration and qualified names
are adapted at module boundaries. See UPSTREAM.md.
-/
module
prelude

import all Init.Data.Nat.Bitwise.Basic
public import SMT.Nat.Xor

public section

namespace SMT.Nat
open _root_.Nat
attribute [local simp] testBit_add_one

/-! ### Arithmetic -/

theorem testBit_two_pow_mul_add (a : Nat) {b i : Nat} (b_lt : b < 2^i) (j : Nat) :
    testBit (2 ^ i * a + b) j =
      if j < i then
        testBit b j
      else
        testBit a (j - i) := by
  cases Nat.lt_or_ge j i with
  | inl j_lt =>
    simp only [j_lt]
    have i_def : i = j + succ (pred (i-j)) := by
      rw [succ_pred_eq_of_pos] <;> omega
    rw [i_def]
    simp only [testBit_eq_decide_div_mod_eq, Nat.pow_add, Nat.mul_assoc]
    simp only [Nat.mul_add_div (Nat.two_pow_pos _)]
    simp [Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_assoc]
  | inr j_ge =>
    have j_def : j = i + (j-i) := (Nat.add_sub_cancel' j_ge).symm
    simp only [
        testBit_eq_decide_div_mod_eq,
        Nat.not_lt_of_le,
        j_ge,
        ite_false]
    simp [congrArg (2^·) j_def, Nat.pow_add,
          ←Nat.div_div_eq_div_mul,
          Nat.mul_add_div,
          Nat.div_eq_of_lt b_lt,
          Nat.two_pow_pos i]

@[grind =]
theorem testBit_two_pow_mul :
    testBit (2 ^ i * a) j = (decide (j ≥ i) && testBit a (j-i)) := by
  have gen := testBit_two_pow_mul_add a (Nat.two_pow_pos i) j
  simp at gen
  rw [gen]
  cases Nat.lt_or_ge j i with
  | _ p => simp [p, Nat.not_le_of_lt, Nat.not_lt_of_le]

@[grind =] -- Ideally `grind` could do this just with `testBit_two_pow_mul`.
theorem testBit_mul_two_pow (x j i : Nat) :
    (x * 2 ^ i).testBit j = (decide (i ≤ j) && x.testBit (j - i)) := by
  rw [Nat.mul_comm, testBit_two_pow_mul]

theorem two_pow_add_eq_or_of_lt {b : Nat} (b_lt : b < 2^i) (a : Nat) :
    2^i * a + b = 2^i * a ||| b := by
  apply eq_of_testBit_eq
  intro j
  simp only [testBit_two_pow_mul_add _ b_lt,
        testBit_or, testBit_two_pow_mul]
  if j_lt : j < i then
    simp [Nat.not_le_of_lt, j_lt]
  else
    have i_le : i ≤ j := Nat.le_of_not_lt j_lt
    have b_lt_j :=
            calc b < 2 ^ i := b_lt
                 _ ≤ 2 ^ j := Nat.pow_le_pow_right Nat.zero_lt_two i_le
    simp [i_le, j_lt, testBit_lt_two_pow, b_lt_j]

theorem or_two_pow_eq_add_of_lt {a n : Nat} (h : a < 2 ^ n) : a ||| 2 ^ n = a + 2 ^ n := by
  have h' := SMT.Nat.two_pow_add_eq_or_of_lt h 1
  simp only [Nat.mul_one] at h'
  rw [SMT.Nat.or_comm, ← h', Nat.add_comm]


end SMT.Nat
