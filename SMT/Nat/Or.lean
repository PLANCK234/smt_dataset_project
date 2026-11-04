/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Author: Joe Hendrix.
Extracted from Lean v4.34.1, Init/Data/Nat/Bitwise/Lemmas.lean:561-646.
Changes: split modules; namespace Nat → SMT.Nat; cross-module helpers made public.
Original theorem names are retained; local simp registration and qualified names
are adapted at module boundaries. See UPSTREAM.md.
-/
module
prelude

import all Init.Data.Nat.Bitwise.Basic
public import SMT.Nat.And

public section

namespace SMT.Nat
open _root_.Nat
attribute [local simp] testBit_add_one

/-! ### lor -/

@[simp, grind =] theorem zero_or (x : Nat) : 0 ||| x = x := by
  simp only [HOr.hOr, OrOp.or, lor]
  unfold bitwise
  simp

@[simp, grind =] theorem or_zero (x : Nat) : x ||| 0 = x := by
  simp only [HOr.hOr, OrOp.or, lor]
  unfold bitwise
  simp [@eq_comm _ 0]

@[simp, grind =] theorem testBit_or (x y i : Nat) : (x ||| y).testBit i = (x.testBit i || y.testBit i) := by
  simp [HOr.hOr, OrOp.or, lor, testBit_bitwise ]

@[simp, grind =] protected theorem or_self (x : Nat) : x ||| x = x := by
   apply SMT.Nat.eq_of_testBit_eq
   simp

@[grind =]
protected theorem or_comm (x y : Nat) : x ||| y = y ||| x := by
   apply SMT.Nat.eq_of_testBit_eq
   simp [Bool.or_comm]

@[grind _=_]
protected theorem or_assoc (x y z : Nat) : (x ||| y) ||| z = x ||| (y ||| z) := by
   apply SMT.Nat.eq_of_testBit_eq
   simp [Bool.or_assoc]

@[grind =]
theorem and_or_distrib_left (x y z : Nat) : x &&& (y ||| z) = (x &&& y) ||| (x &&& z) := by
   apply SMT.Nat.eq_of_testBit_eq
   simp [Bool.and_or_distrib_left]

@[grind =]
theorem and_or_distrib_right (x y z : Nat) : (x ||| y) &&& z = (x &&& z) ||| (y &&& z) := by
   apply SMT.Nat.eq_of_testBit_eq
   simp [Bool.and_or_distrib_right]

theorem or_and_distrib_left (x y z : Nat) : x ||| (y &&& z) = (x ||| y) &&& (x ||| z) := by
   apply SMT.Nat.eq_of_testBit_eq
   simp [Bool.or_and_distrib_left]

theorem or_and_distrib_right (x y z : Nat) : (x &&& y) ||| z = (x ||| z) &&& (y ||| z) := by
   apply SMT.Nat.eq_of_testBit_eq
   simp [Bool.or_and_distrib_right]

instance : Std.Associative (α := Nat) (· ||| ·) where
  assoc := SMT.Nat.or_assoc

instance : Std.Commutative (α := Nat) (· ||| ·) where
  comm := SMT.Nat.or_comm

instance : Std.IdempotentOp (α := Nat) (· ||| ·) where
  idempotent := SMT.Nat.or_self

instance : Std.LawfulCommIdentity (α := Nat) (· ||| ·) 0 where
  left_id := zero_or
  right_id := or_zero

theorem or_lt_two_pow {x y n : Nat} (left : x < 2^n) (right : y < 2^n) : x ||| y < 2^n :=
  bitwise_lt_two_pow left right

@[simp] theorem or_mod_two_eq_one : (a ||| b) % 2 = 1 ↔ a % 2 = 1 ∨ b % 2 = 1 := by
  simp only [mod_two_eq_one_iff_testBit_zero]
  rw [testBit_or]
  simp

theorem or_div_two_pow : (a ||| b) / 2 ^ n = a / 2 ^ n ||| b / 2 ^ n :=
  bitwise_div_two_pow

theorem or_div_two : (a ||| b) / 2 = a / 2 ||| b / 2 :=
  or_div_two_pow (n := 1)

theorem or_mod_two_pow : (a ||| b) % 2 ^ n = a % 2 ^ n ||| b % 2 ^ n :=
  bitwise_mod_two_pow

@[simp]
theorem or_eq_zero_iff {n m : Nat} : n ||| m = 0 ↔ n = 0 ∧ m = 0 := by
  simp [SMT.Nat.eq_iff_testBit_eq, forall_and]

@[simp]
theorem or_pos_iff {n m : Nat} : 0 < n ||| m ↔ 0 < n ∨ 0 < m := by
  rw [Nat.pos_iff_ne_zero, ne_eq, SMT.Nat.or_eq_zero_iff, Decidable.not_and_iff_not_or_not,
    Nat.pos_iff_ne_zero, Nat.pos_iff_ne_zero]


end SMT.Nat
