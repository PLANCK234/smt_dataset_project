/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Author: Joe Hendrix.
Extracted from Lean v4.34.1, Init/Data/Nat/Bitwise/Lemmas.lean:404-493.
Changes: split modules; namespace Nat → SMT.Nat; cross-module helpers made public.
Original theorem names are retained; local simp registration and qualified names
are adapted at module boundaries. See UPSTREAM.md.
-/
module
prelude

import all Init.Data.Nat.Bitwise.Basic
public import SMT.Nat.TestBit

public section

namespace SMT.Nat
open _root_.Nat
attribute [local simp] testBit_add_one

/-! ### bitwise -/

theorem testBit_bitwise (of_false_false : f false false = false) (x y i : Nat) :
    (bitwise f x y).testBit i = f (x.testBit i) (y.testBit i) := by
  induction i using Nat.strongRecOn generalizing x y with
  | ind i hyp =>
    unfold bitwise
    if x_zero : x = 0 then
      cases p : f false true <;>
        cases yi : testBit y i <;>
          simp [x_zero, p, yi, of_false_false]
    else if y_zero : y = 0 then
      simp [x_zero, y_zero]
      cases p : f true false <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;>
        cases testBit x i <;>
          simp [p, of_false_false]
    else
      simp only [x_zero, y_zero, ←Nat.two_mul]
      cases i with
      | zero =>
        cases p : f (decide (x % 2 = 1)) (decide (y % 2 = 1)) <;>
          simp [p]
      | succ i =>
        have hyp_i := hyp i (Nat.le_refl (i+1))
        cases p : f (decide (x % 2 = 1)) (decide (y % 2 = 1)) <;>
          simp [hyp_i, Nat.mul_add_div]

/-! ### bitwise -/

@[local simp]
theorem eq_0_of_lt_one (x : Nat) : x < 1 ↔ x = 0 :=
  Iff.intro
    (fun p =>
      match x with
      | 0 => Eq.refl 0
      | _+1 => False.elim (not_lt_zero _ (Nat.lt_of_succ_lt_succ p)))
    (fun p => by simp [p])

theorem eq_0_of_lt (x : Nat) : x < 2^ 0 ↔ x = 0 := eq_0_of_lt_one x

@[local simp]
theorem zero_lt_pow (n : Nat) : 0 < 2^n := by
  induction n
  case zero => simp
  case succ n hyp => simpa [Nat.pow_succ]

theorem div_two_le_of_lt_two {m n : Nat} (p : m < 2 ^ succ n) : m / 2 < 2^n := by
  simp [div_lt_iff_lt_mul Nat.zero_lt_two]
  exact p

/-- This provides a bound on bitwise operations. -/
theorem bitwise_lt_two_pow (left : x < 2^n) (right : y < 2^n) : (Nat.bitwise f x y) < 2^n := by
  induction n generalizing x y with
  | zero =>
    simp only [eq_0_of_lt] at left right
    unfold bitwise
    simp [left, right]
  | succ n hyp =>
    unfold bitwise
    if x_zero : x = 0 then
      simp only [x_zero, ite_eq_left]
      by_cases p : f false true = true <;> simp [p, right]
    else if y_zero : y = 0 then
      simp only [x_zero, y_zero, ite_eq_left]
      by_cases p : f true false = true <;> simp [p, left]
    else
      simp only [x_zero, y_zero]
      have hyp1 := hyp (div_two_le_of_lt_two left) (div_two_le_of_lt_two right)
      by_cases p : f (decide (x % 2 = 1)) (decide (y % 2 = 1)) = true <;>
        simp [p, Nat.pow_succ, mul_succ, Nat.add_assoc]
      case pos =>
        apply lt_of_succ_le
        simp only [← Nat.succ_add]
        apply Nat.add_le_add <;> exact hyp1
      case neg =>
        apply Nat.add_lt_add <;> exact hyp1

theorem bitwise_div_two_pow (of_false_false : f false false = false := by rfl) :
  (bitwise f x y) / 2 ^ n = bitwise f (x / 2 ^ n) (y / 2 ^ n) := by
  apply SMT.Nat.eq_of_testBit_eq
  simp [testBit_bitwise of_false_false, testBit_div_two_pow]

theorem bitwise_mod_two_pow (of_false_false : f false false = false := by rfl) :
  (bitwise f x y) % 2 ^ n = bitwise f (x % 2 ^ n) (y % 2 ^ n) := by
  apply SMT.Nat.eq_of_testBit_eq
  simp only [testBit_mod_two_pow, testBit_bitwise of_false_false]
  intro i
  by_cases h : i < n <;> simp only [h, decide_true, decide_false, Bool.true_and, Bool.false_and,
    of_false_false]


end SMT.Nat
