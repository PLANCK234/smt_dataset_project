/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Author: Joe Hendrix.
Extracted from Lean v4.34.1, Init/Data/Nat/Bitwise/Lemmas.lean:776-865.
Changes: split modules; namespace Nat → SMT.Nat; cross-module helpers made public.
Original theorem names are retained; local simp registration and qualified names
are adapted at module boundaries. See UPSTREAM.md.
-/
module
prelude

import all Init.Data.Nat.Bitwise.Basic
public import SMT.Nat.Arithmetic

public section

namespace SMT.Nat
open _root_.Nat
attribute [local simp] testBit_add_one

/-! ### shiftLeft and shiftRight -/

@[simp, grind =] theorem testBit_shiftLeft (x : Nat) : testBit (x <<< i) j =
    (decide (j ≥ i) && testBit x (j-i)) := by
  simp [shiftLeft_eq, Nat.mul_comm _ (2^_), testBit_two_pow_mul]

@[simp, grind =] theorem testBit_shiftRight (x : Nat) : testBit (x >>> i) j = testBit x (i+j) := by
  simp [testBit, ←shiftRight_add]

@[simp] theorem shiftLeft_mod_two_eq_one : x <<< i % 2 = 1 ↔ i = 0 ∧ x % 2 = 1 := by
  rw [mod_two_eq_one_iff_testBit_zero, testBit_shiftLeft]
  simp

theorem bitwise_mul_two_pow (of_false_false : f false false = false := by rfl) :
    (bitwise f x y) * 2 ^ n = bitwise f (x * 2 ^ n) (y * 2 ^ n) := by
  apply SMT.Nat.eq_of_testBit_eq
  simp only [testBit_mul_two_pow, testBit_bitwise of_false_false]
  intro i
  by_cases hn : n ≤ i
  · simp [hn]
  · simp [hn, of_false_false]

@[grind _=_]
theorem shiftLeft_bitwise_distrib {a b : Nat} (of_false_false : f false false = false := by rfl) :
    (bitwise f a b) <<< i = bitwise f (a <<< i) (b <<< i) := by
  simp [shiftLeft_eq, bitwise_mul_two_pow of_false_false]

@[grind _=_]
theorem shiftLeft_and_distrib {a b : Nat} : (a &&& b) <<< i = a <<< i &&& b <<< i :=
  shiftLeft_bitwise_distrib

@[grind _=_]
theorem shiftLeft_or_distrib {a b : Nat} : (a ||| b) <<< i = a <<< i ||| b <<< i :=
  shiftLeft_bitwise_distrib

@[grind _=_]
theorem shiftLeft_xor_distrib {a b : Nat} : (a ^^^ b) <<< i = a <<< i ^^^ b <<< i :=
  shiftLeft_bitwise_distrib

@[simp] theorem decide_shiftRight_mod_two_eq_one :
    decide (x >>> i % 2 = 1) = x.testBit i := by
  simp only [testBit, one_and_eq_mod_two, mod_two_bne_zero]
  exact (Bool.beq_eq_decide_eq _ _).symm

@[grind _=_]
theorem shiftRight_bitwise_distrib {a b : Nat} (of_false_false : f false false = false := by rfl) :
    (bitwise f a b) >>> i = bitwise f (a >>> i) (b >>> i) := by
  simp [shiftRight_eq_div_pow, bitwise_div_two_pow of_false_false]

@[grind _=_]
theorem shiftRight_and_distrib {a b : Nat} : (a &&& b) >>> i = a >>> i &&& b >>> i :=
  shiftRight_bitwise_distrib

@[grind _=_]
theorem shiftRight_or_distrib {a b : Nat} : (a ||| b) >>> i = a >>> i ||| b >>> i :=
  shiftRight_bitwise_distrib

@[grind _=_]
theorem shiftRight_xor_distrib {a b : Nat} : (a ^^^ b) >>> i = a >>> i ^^^ b >>> i :=
  shiftRight_bitwise_distrib

theorem mod_two_pow_shiftLeft_mod_two_pow {a b c : Nat} : ((a % 2 ^ c) <<< b) % 2 ^ c = (a <<< b) % 2 ^ c := by
  apply SMT.Nat.eq_of_testBit_eq
  simp only [testBit_mod_two_pow, testBit_shiftLeft, ge_iff_le]
  intro i
  by_cases hic : i < c
  · simp [(by omega : i - b < c)]
  · simp [*]

theorem le_shiftLeft {a b : Nat} : a ≤ a <<< b :=
  shiftLeft_eq _ _ ▸ Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)

theorem lt_of_shiftLeft_lt {a b c : Nat} (h : a <<< b < c) : a < c :=
  Nat.lt_of_le_of_lt le_shiftLeft h

theorem shiftLeft_add_eq_or_of_lt {b : Nat} (b_lt : b < 2^i) (a : Nat) :
    a <<< i + b = a <<< i ||| b := by
  rw [shiftLeft_eq, Nat.mul_comm]
  rw [two_pow_add_eq_or_of_lt b_lt]

@[simp]
theorem shiftLeft_eq_zero_iff {a n : Nat} : a <<< n = 0 ↔ a = 0 := by
  simp [shiftLeft_eq, mul_eq_zero]

@[simp]
theorem shiftLeft_pos_iff {n m : Nat} : 0 < n <<< m ↔ 0 < n := by
  simp [Nat.pos_iff_ne_zero]

instance {a n : Nat} [NeZero a] : NeZero (a <<< n) := ⟨mt shiftLeft_eq_zero_iff.mp (NeZero.ne _)⟩


end SMT.Nat
