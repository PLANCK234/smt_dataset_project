/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Author: Joe Hendrix.
Extracted from Lean v4.34.1, Init/Data/Nat/Bitwise/Lemmas.lean:647-711.
Changes: split modules; namespace Nat → SMT.Nat; cross-module helpers made public.
Original theorem names are retained; local simp registration and qualified names
are adapted at module boundaries. See UPSTREAM.md.
-/
module
prelude

import all Init.Data.Nat.Bitwise.Basic
public import SMT.Nat.Or

public section

namespace SMT.Nat
open _root_.Nat
attribute [local simp] testBit_add_one

/-! ### xor -/

@[simp, grind =] theorem testBit_xor (x y i : Nat) :
    (x ^^^ y).testBit i = ((x.testBit i) ^^ (y.testBit i)) := by
  simp [HXor.hXor, XorOp.xor, Nat.xor, testBit_bitwise ]

@[simp, grind =] theorem zero_xor (x : Nat) : 0 ^^^ x = x := by
   apply SMT.Nat.eq_of_testBit_eq
   simp

@[simp, grind =] theorem xor_zero (x : Nat) : x ^^^ 0 = x := by
   apply SMT.Nat.eq_of_testBit_eq
   simp

@[simp, grind =] protected theorem xor_self (x : Nat) : x ^^^ x = 0 := by
   apply SMT.Nat.eq_of_testBit_eq
   simp

@[grind =]
protected theorem xor_comm (x y : Nat) : x ^^^ y = y ^^^ x := by
   apply SMT.Nat.eq_of_testBit_eq
   simp [Bool.xor_comm]

@[grind _=_]
protected theorem xor_assoc (x y z : Nat) : (x ^^^ y) ^^^ z = x ^^^ (y ^^^ z) := by
   apply SMT.Nat.eq_of_testBit_eq
   simp

instance : Std.Associative (α := Nat) (· ^^^ ·) where
  assoc := SMT.Nat.xor_assoc

instance : Std.Commutative (α := Nat) (· ^^^ ·) where
  comm := SMT.Nat.xor_comm

instance : Std.LawfulCommIdentity (α := Nat) (· ^^^ ·) 0 where
  left_id := zero_xor
  right_id := xor_zero

theorem xor_lt_two_pow {x y n : Nat} (left : x < 2^n) (right : y < 2^n) : x ^^^ y < 2^n :=
  bitwise_lt_two_pow left right

@[grind =]
theorem and_xor_distrib_right {a b c : Nat} : (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) := by
  apply SMT.Nat.eq_of_testBit_eq
  simp [Bool.and_xor_distrib_right]

@[grind =]
theorem and_xor_distrib_left {a b c : Nat} : a &&& (b ^^^ c) = (a &&& b) ^^^ (a &&& c) := by
  apply SMT.Nat.eq_of_testBit_eq
  simp [Bool.and_xor_distrib_left]

@[simp] theorem xor_mod_two_eq_one : ((a ^^^ b) % 2 = 1) ↔ ¬ ((a % 2 = 1) ↔ (b % 2 = 1)) := by
  simp only [mod_two_eq_one_iff_testBit_zero]
  rw [testBit_xor]
  simp

theorem xor_div_two_pow : (a ^^^ b) / 2 ^ n = a / 2 ^ n ^^^ b / 2 ^ n :=
  bitwise_div_two_pow

theorem xor_div_two : (a ^^^ b) / 2 = a / 2 ^^^ b / 2 :=
  xor_div_two_pow (n := 1)

theorem xor_mod_two_pow : (a ^^^ b) % 2 ^ n = a % 2 ^ n ^^^ b % 2 ^ n :=
  bitwise_mod_two_pow


end SMT.Nat
