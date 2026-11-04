/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Author: Joe Hendrix.
Extracted from Lean v4.34.1, Init/Data/Nat/Bitwise/Lemmas.lean:494-560.
Changes: split modules; namespace Nat → SMT.Nat; cross-module helpers made public.
Original theorem names are retained; local simp registration and qualified names
are adapted at module boundaries. See UPSTREAM.md.
-/
module
prelude

import all Init.Data.Nat.Bitwise.Basic
public import SMT.Nat.Bitwise

public section

namespace SMT.Nat
open _root_.Nat
attribute [local simp] testBit_add_one

/-! ### and -/

@[simp, grind =] theorem testBit_and (x y i : Nat) : (x &&& y).testBit i = (x.testBit i && y.testBit i) := by
  simp [HAnd.hAnd, AndOp.and, land, testBit_bitwise ]


@[simp, grind =] protected theorem and_self (x : Nat) : x &&& x = x := by
   apply SMT.Nat.eq_of_testBit_eq
   simp

@[grind =]
protected theorem and_comm (x y : Nat) : x &&& y = y &&& x := by
   apply SMT.Nat.eq_of_testBit_eq
   simp [Bool.and_comm]

protected theorem and_assoc (x y z : Nat) : (x &&& y) &&& z = x &&& (y &&& z) := by
   apply SMT.Nat.eq_of_testBit_eq
   simp [Bool.and_assoc]

grind_pattern SMT.Nat.and_assoc => (x &&& y) &&& z where
  x =/= 0; y =/= 0; z =/= 0

grind_pattern SMT.Nat.and_assoc => x &&& (y &&& z) where
  x =/= 0; y =/= 0; z =/= 0

instance : Std.Associative (α := Nat) (· &&& ·) where
  assoc := SMT.Nat.and_assoc

instance : Std.Commutative (α := Nat) (· &&& ·) where
  comm := SMT.Nat.and_comm

instance : Std.IdempotentOp (α := Nat) (· &&& ·) where
  idempotent := SMT.Nat.and_self

theorem and_lt_two_pow (x : Nat) {y n : Nat} (right : y < 2^n) : (x &&& y) < 2^n := by
  apply lt_pow_two_of_testBit
  intro i i_ge_n
  have yf : testBit y i = false := by
          apply SMT.Nat.testBit_lt_two_pow
          apply Nat.lt_of_lt_of_le right
          exact Nat.pow_le_pow_right Nat.zero_lt_two i_ge_n
  simp [yf]

@[simp] theorem and_two_pow_sub_one_eq_mod (x n : Nat) : x &&& 2^n - 1 = x % 2^n := by
  apply eq_of_testBit_eq
  intro i
  simp only [testBit_and, testBit_mod_two_pow]
  cases testBit x i <;> simp

theorem and_two_pow_sub_one_of_lt_two_pow {x : Nat} (lt : x < 2^n) : x &&& 2^n - 1 = x := by
  rw [and_two_pow_sub_one_eq_mod]
  apply Nat.mod_eq_of_lt lt

@[simp] theorem and_mod_two_eq_one : (a &&& b) % 2 = 1 ↔ a % 2 = 1 ∧ b % 2 = 1 := by
  simp only [mod_two_eq_one_iff_testBit_zero]
  rw [testBit_and]
  simp

theorem and_div_two_pow : (a &&& b) / 2 ^ n = a / 2 ^ n &&& b / 2 ^ n :=
  bitwise_div_two_pow

theorem and_div_two : (a &&& b) / 2 = a / 2 &&& b / 2 :=
  and_div_two_pow (n := 1)

theorem and_mod_two_pow : (a &&& b) % 2 ^ n = (a % 2 ^ n) &&& (b % 2 ^ n) :=
  bitwise_mod_two_pow


end SMT.Nat
