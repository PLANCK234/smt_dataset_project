/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Upstream authors: Markus Himmel, Alex Keizer, Praneeth Kolichala.
Adapted from mathlib v4.34.1, d13f23b723b8a846827a245b89c10fc7d3f11612:
  Mathlib/Data/Nat/Bitwise.lean and Mathlib/Data/Nat/Bits.lean.
Changes: namespace SMT.Nat; Nat instead of ℕ; proofs use extracted/core lemmas;
parity is expressed using bits and % 2, without algebraic parity typeclasses.
No Mathlib or Batteries dependency is required.
-/
module
prelude
public import Init.Data.Nat.Mod

import all Init.Data.Nat.Bitwise.Basic
public import SMT.Nat.Shift

public section
namespace SMT.Nat
open _root_.Nat

-- Mathlib.Data.Nat.Bitwise: elementary truth-table equations.
theorem bitwise_zero_left {f : Bool → Bool → Bool} (m : Nat) :
    bitwise f 0 m = if f false true then m else 0 := by simp [bitwise]
theorem bitwise_zero_right {f : Bool → Bool → Bool} (n : Nat) :
    bitwise f n 0 = if f true false then n else 0 := by
  unfold bitwise
  by_cases h : n = 0 <;> simp [h]
theorem bitwise_zero {f : Bool → Bool → Bool} : bitwise f 0 0 = 0 := by
  simp [bitwise_zero_right]
theorem testBit_lor (m n k : Nat) : (m ||| n).testBit k = (m.testBit k || n.testBit k) :=
  testBit_or m n k
theorem testBit_land (m n k : Nat) : (m &&& n).testBit k = (m.testBit k && n.testBit k) :=
  testBit_and m n k

theorem zero_of_testBit_eq_false {n : Nat} (h : ∀ i, n.testBit i = false) : n = 0 :=
  eq_of_testBit_eq fun i => (h i).trans (zero_testBit i).symm
theorem testBit_eq_false_of_lt {n i : Nat} (h : n < 2 ^ i) : n.testBit i = false := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]

theorem lor_comm (n m : Nat) : n ||| m = m ||| n := SMT.Nat.or_comm n m
theorem land_comm (n m : Nat) : n &&& m = m &&& n := SMT.Nat.and_comm n m
theorem land_assoc (n m k : Nat) : (n &&& m) &&& k = n &&& (m &&& k) := SMT.Nat.and_assoc n m k
theorem lor_assoc (n m k : Nat) : (n ||| m) ||| k = n ||| (m ||| k) := SMT.Nat.or_assoc n m k

/-- Mathlib.Data.Nat.Bitwise.and_two_pow. -/
theorem and_two_pow (n i : Nat) : n &&& 2 ^ i = (n.testBit i).toNat * 2 ^ i := by
  apply eq_of_testBit_eq
  intro j
  by_cases hij : i = j
  · subst j
    cases h : n.testBit i <;> simp [h]
  · cases h : n.testBit i <;> simp [testBit_two_pow_of_ne hij]
theorem two_pow_and (n i : Nat) : 2 ^ i &&& n = 2 ^ i * (n.testBit i).toNat := by
  rw [Nat.mul_comm, land_comm, and_two_pow]

theorem shiftLeft_lt {x n m : Nat} (h : x < 2 ^ n) : x <<< m < 2 ^ (n + m) := by
  simp only [Nat.pow_add, Nat.shiftLeft_eq, Nat.mul_lt_mul_right (Nat.two_pow_pos _), h]
/-- Width bound for concatenating two unsigned values. -/
theorem append_lt {x y n m : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ m) :
    y <<< n ||| x < 2 ^ (n + m) := by
  apply or_lt_two_pow
  · rw [Nat.add_comm]; exact shiftLeft_lt hy
  · exact Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))

/-- Mathlib.Data.Nat.Bitwise.xor_mod_two_eq, proved using the extracted bit test rules. -/
theorem xor_mod_two_eq {m n : Nat} : (m ^^^ n) % 2 = (m + n) % 2 := by
  have h := @xor_mod_two_eq_one m n
  have hm := Nat.mod_two_eq_zero_or_one m
  have hn := Nat.mod_two_eq_zero_or_one n
  have hx := Nat.mod_two_eq_zero_or_one (m ^^^ n)
  rw [Nat.add_mod]
  omega

-- Mathlib.Data.Nat.Bits: the numerical helpers used by bitwise proofs.
@[expose] def div2 (n : Nat) : Nat := n / 2
@[expose] def bodd (n : Nat) : Bool := n.testBit 0
@[expose] def ldiff (m n : Nat) : Nat := Nat.bitwise (fun a b => a && !b) m n

theorem div2_val (n : Nat) : div2 n = n / 2 := rfl
theorem div2_zero : div2 0 = 0 := rfl
theorem div2_one : div2 1 = 0 := rfl
theorem div2_two : div2 2 = 1 := rfl
theorem bodd_zero : bodd 0 = false := rfl
theorem bodd_one : bodd 1 = true := rfl
theorem bodd_two : bodd 2 = false := rfl
theorem mod_two_of_bodd (n : Nat) : n % 2 = (bodd n).toNat := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [bodd, h]
theorem bodd_succ (n : Nat) : bodd (n + 1) = !(bodd n) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
    simp [bodd, Nat.add_mod, h]
theorem bodd_add (m n : Nat) : bodd (m + n) = Bool.xor (bodd m) (bodd n) := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
      simp [bodd, Nat.add_mod, hm, hn]
theorem bodd_mul (m n : Nat) : bodd (m * n) = (bodd m && bodd n) := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
      simp [bodd, Nat.mul_mod, hm, hn]
theorem bodd_add_div2 (n : Nat) : (bodd n).toNat + 2 * div2 n = n := by
  rw [← mod_two_of_bodd, div2_val]
  omega
theorem testBit_ldiff (m n k : Nat) :
    (ldiff m n).testBit k = (m.testBit k && !(n.testBit k)) :=
  testBit_bitwise (by decide) m n k

end SMT.Nat
