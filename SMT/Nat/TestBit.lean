/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Author: Joe Hendrix.
Extracted from Lean v4.34.1, Init/Data/Nat/Bitwise/Lemmas.lean:87-403.
Changes: split modules; namespace Nat → SMT.Nat; cross-module helpers made public.
Original theorem names are retained; local simp registration and qualified names
are adapted at module boundaries. See UPSTREAM.md.
-/
module
prelude

import all Init.Data.Nat.Bitwise.Basic
public import SMT.Nat.Basic

public section

namespace SMT.Nat
open _root_.Nat

/-! ### testBit -/

@[simp, grind =] theorem zero_testBit (i : Nat) : testBit 0 i = false := by
  simp only [testBit, zero_shiftRight, and_zero, bne_self_eq_false]

@[simp, grind =] theorem testBit_zero (x : Nat) : testBit x 0 = decide (x % 2 = 1) := by
  cases mod_two_eq_zero_or_one x with | _ p => simp [testBit, p]

theorem mod_two_eq_one_iff_testBit_zero : (x % 2 = 1) ↔ x.testBit 0 = true := by
  cases mod_two_eq_zero_or_one x <;> simp_all

theorem mod_two_eq_zero_iff_testBit_zero : (x % 2 = 0) ↔ x.testBit 0 = false := by
  cases mod_two_eq_zero_or_one x <;> simp_all

theorem testBit_succ (x i : Nat) : testBit x (succ i) = testBit (x/2) i := by
  unfold testBit
  simp [shiftRight_succ_inside]

/--
Depending on use cases either `testBit_add_one` or `testBit_div_two`
may be more useful as a `simp` lemma, so neither is a global `simp` lemma.
-/
-- We turn `testBit_add_one` on as a `local simp` for this file.
@[local simp, grind _=_]
theorem testBit_add_one (x i : Nat) : testBit x (i + 1) = testBit (x/2) i := by
  unfold testBit
  simp [shiftRight_succ_inside]

@[grind _=_]
theorem testBit_add (x i n : Nat) : testBit x (i + n) = testBit (x / 2 ^ n) i := by
  revert x
  induction n with
  | zero => simp
  | succ n ih =>
    intro x
    rw [← Nat.add_assoc, testBit_add_one, ih (x / 2),
      Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem testBit_div_two (x i : Nat) : testBit (x / 2) i = testBit x (i + 1) := by
  simp

theorem testBit_div_two_pow (x i : Nat) : testBit (x / 2 ^ n) i = testBit x (i + n) :=
  testBit_add .. |>.symm

@[grind =]
theorem testBit_eq_decide_div_mod_eq {x : Nat} : testBit x i = decide (x / 2^i % 2 = 1) := by
  induction i generalizing x with
  | zero =>
    unfold testBit
    cases mod_two_eq_zero_or_one x with | _ xz => simp [xz]
  | succ i hyp =>
    simp [hyp, Nat.div_div_eq_div_mul, Nat.pow_succ']

theorem toNat_testBit (x i : Nat) :
    (x.testBit i).toNat = x / 2 ^ i % 2 := by
  rw [testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2^i) <;> simp_all

theorem exists_testBit_of_ne_zero {x : Nat} (xnz : x ≠ 0) : ∃ i, testBit x i := by
  induction x using div2Induction with
  | ind x hyp =>
    have x_pos : x > 0 := Nat.pos_of_ne_zero xnz
    match mod_two_eq_zero_or_one x with
    | Or.inl mod2_eq =>
      rw [←div_add_mod x 2] at xnz
      simp only [mod2_eq, ne_eq, Nat.mul_eq_zero, Nat.add_zero, false_or, reduceCtorEq] at xnz
      have ⟨d, dif⟩   := hyp x_pos xnz
      apply Exists.intro (d+1)
      simp_all
    | Or.inr mod2_eq =>
      apply Exists.intro 0
      simp_all

theorem exists_testBit_ne_of_ne {x y : Nat} (p : x ≠ y) : ∃ i, testBit x i ≠ testBit y i := by
  induction y using SMT.Nat.div2Induction generalizing x with
  | ind y hyp =>
    cases Nat.eq_zero_or_pos y with
    | inl yz =>
      simp only [yz, SMT.Nat.zero_testBit]
      simp only [yz] at p
      have ⟨i,ip⟩  := exists_testBit_of_ne_zero p
      apply Exists.intro i
      simp [ip]
    | inr ypos =>
      if lsb_diff : x % 2 = y % 2 then
        rw [←Nat.div_add_mod x 2, ←Nat.div_add_mod y 2] at p
        simp only [ne_eq, lsb_diff, Nat.add_right_cancel_iff,
          Nat.zero_lt_succ, Nat.mul_left_cancel_iff] at p
        have ⟨i, ieq⟩  := hyp ypos p
        apply Exists.intro (i+1)
        simpa
      else
        apply Exists.intro 0
        simp only [testBit_zero]
        revert lsb_diff
        cases mod_two_eq_zero_or_one x with
        | _ p => cases mod_two_eq_zero_or_one y with | _ q => simp [p,q]

/--
`eq_of_testBit_eq` allows proving two natural numbers are equal
if their bits are all equal.
-/
theorem eq_of_testBit_eq {x y : Nat} (pred : ∀i, testBit x i = testBit y i) : x = y := by
  if h : x = y then
    exact h
  else
    let ⟨i,eq⟩ := exists_testBit_ne_of_ne h
    have p := pred i
    contradiction

theorem eq_iff_testBit_eq {n m : Nat} : n = m ↔ ∀ i, Nat.testBit n i = Nat.testBit m i := by
  refine ⟨?_, SMT.Nat.eq_of_testBit_eq⟩
  rintro rfl
  simp

theorem exists_ge_and_testBit_of_ge_two_pow {x : Nat} (p : x ≥ 2^n) : ∃ i ≥ n, testBit x i := by
  induction x using div2Induction generalizing n with
  | ind x hyp =>
    have x_pos : x > 0 := Nat.lt_of_lt_of_le (Nat.two_pow_pos n) p
    have x_ne_zero : x ≠ 0 := Nat.ne_of_gt x_pos
    match n with
    | zero =>
      let ⟨j, jp⟩ := exists_testBit_of_ne_zero x_ne_zero
      exact Exists.intro j (And.intro (Nat.zero_le _) jp)
    | succ n =>
      have x_ge_n : x / 2 ≥ 2 ^ n := by
          simpa [le_div_iff_mul_le, ← Nat.pow_succ'] using! p
      have ⟨j, jp⟩ := @hyp x_pos n x_ge_n
      apply Exists.intro (j+1)
      apply And.intro
      case left =>
        exact (Nat.succ_le_succ jp.left)
      case right =>
        simpa using jp.right

theorem ge_two_pow_of_testBit {x : Nat} (p : testBit x i = true) : x ≥ 2^i := by
  simp only [SMT.Nat.testBit_eq_decide_div_mod_eq] at p
  apply Decidable.by_contra
  intro not_ge
  have x_lt : x < 2^i := Nat.lt_of_not_le not_ge
  simp [div_eq_of_lt x_lt] at p

theorem testBit_lt_two_pow {x i : Nat} (lt : x < 2^i) : x.testBit i = false := by
  match p : x.testBit i with
  | false => trivial
  | true =>
    exfalso
    exact Nat.not_le_of_gt lt (ge_two_pow_of_testBit p)

theorem testBit_of_two_pow_le_and_two_pow_add_one_gt {n i : Nat}
    (hle : 2^i ≤ n) (hgt : n < 2^(i + 1)) : n.testBit i = true := by
  rcases exists_ge_and_testBit_of_ge_two_pow hle with ⟨i', ⟨_, _⟩⟩
  have : i = i' := by
    false_or_by_contra
    have : 2 ^ (i + 1) ≤ 2 ^ i' := Nat.pow_le_pow_of_le (by decide) (by omega)
    have : n.testBit i' = false := testBit_lt_two_pow (by omega)
    simp_all only [Bool.false_eq_true]
  rwa [this]

theorem lt_pow_two_of_testBit (x : Nat) (p : ∀i, i ≥ n → testBit x i = false) : x < 2^n := by
  apply Decidable.by_contra
  intro not_lt
  have x_ge_n := Nat.ge_of_not_lt not_lt
  have ⟨i, ⟨i_ge_n, test_true⟩⟩ := exists_ge_and_testBit_of_ge_two_pow x_ge_n
  have test_false := p _ i_ge_n
  simp [test_true] at test_false

theorem testBit_log2 {n : Nat} (h : n ≠ 0) : n.testBit n.log2 = true := by
  have := log2_eq_iff (n := n) (k := n.log2) (by omega)
  apply testBit_of_two_pow_le_and_two_pow_add_one_gt <;> omega

theorem succ_mod_two : succ x % 2 = 1 - x % 2 := by
  induction x with
  | zero =>
    trivial
  | succ x hyp =>
    have p : 2 ≤ x + 2 := Nat.le_add_left _ _
    simp [Nat.mod_eq_ite (x+2) 2, p, hyp]
    cases Nat.mod_two_eq_zero_or_one x with | _ p => simp [p]

theorem testBit_succ_zero : testBit (x + 1) 0 = !(testBit x 0) := by
  simp only [testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one, succ_mod_two]
  cases Nat.mod_two_eq_zero_or_one x with | _ p => simp [p]

theorem testBit_two_pow_add_eq (x i : Nat) : testBit (2^i + x) i = !(testBit x i) := by
  simp only [testBit_eq_decide_div_mod_eq, add_div_left, Nat.two_pow_pos, succ_mod_two]
  cases mod_two_eq_zero_or_one (x / 2 ^ i) with
  | _ p => simp [p]

theorem testBit_mul_two_pow_add_eq (a b i : Nat) :
    testBit (2^i*a + b) i = (a%2 = 1 ^^ testBit b i) := by
  match a with
  | 0 => simp
  | a+1 =>
    simp [Nat.mul_succ, Nat.add_assoc,
          testBit_mul_two_pow_add_eq a,
          testBit_two_pow_add_eq,
          SMT.Nat.succ_mod_two]
    cases mod_two_eq_zero_or_one a with | _ p => simp [p]

theorem testBit_two_pow_add_gt {i j : Nat} (j_lt_i : j < i) (x : Nat) :
    testBit (2^i + x) j = testBit x j := by
  have i_def : i = j + (i-j) := (Nat.add_sub_cancel' (Nat.le_of_lt j_lt_i)).symm
  rw [i_def]
  simp only [testBit_eq_decide_div_mod_eq, Nat.pow_add,
        Nat.mul_add_div (Nat.two_pow_pos _)]
  match i_sub_j_eq : i - j with
  | 0 =>
    exfalso
    rw [Nat.sub_eq_zero_iff_le] at i_sub_j_eq
    exact Nat.not_le_of_gt j_lt_i i_sub_j_eq
  | d+1 =>
    simp [Nat.pow_succ, Nat.mul_comm _ 2]

@[simp, grind =] theorem testBit_mod_two_pow (x j i : Nat) :
    testBit (x % 2^j) i = (decide (i < j) && testBit x i) := by
  induction x using Nat.strongRecOn generalizing j i with
  | ind x hyp =>
    rw [mod_eq_ite]
    rcases Nat.lt_or_ge x (2^j) with x_lt_j | x_ge_j
    · have not_j_le_x := Nat.not_le_of_gt x_lt_j
      simp [not_j_le_x]
      rcases Nat.lt_or_ge i j with i_lt_j | i_ge_j
      · simp [i_lt_j]
      · have x_lt : x < 2^i :=
            calc x < 2^j := x_lt_j
                _ ≤ 2^i := Nat.pow_le_pow_right Nat.zero_lt_two i_ge_j
        simp [SMT.Nat.testBit_lt_two_pow x_lt]
    · generalize y_eq : x - 2^j = y
      have x_eq : x = y + 2^j := Nat.eq_add_of_sub_eq x_ge_j y_eq
      simp only [Nat.two_pow_pos, x_eq, Nat.le_add_left, true_and, ite_true]
      have y_lt_x : y < x := by
        simp only [x_eq, Nat.lt_add_right_iff_pos]
        exact Nat.two_pow_pos j
      simp only [hyp y y_lt_x]
      if i_lt_j : i < j then
        rw [Nat.add_comm _ (2^_), testBit_two_pow_add_gt i_lt_j]
      else
        simp [i_lt_j]

theorem testBit_one_zero : testBit 1 0 = true := by trivial

theorem not_decide_mod_two_eq_one (x : Nat)
    : (!decide (x % 2 = 1)) = decide (x % 2 = 0) := by
  cases Nat.mod_two_eq_zero_or_one x <;> (rename_i p; simp [p])

@[grind =]
theorem testBit_two_pow_sub_succ (h₂ : x < 2 ^ n) (i : Nat) :
    testBit (2^n - (x + 1)) i = (decide (i < n) && ! testBit x i) := by
  induction i generalizing n x with
  | zero =>
    match n with
    | 0 => simp
    | n+1 =>
      simp [not_decide_mod_two_eq_one]
      omega
  | succ i ih =>
    simp only [testBit_succ]
    match n with
    | 0 =>
      simp [decide_eq_false]
    | n+1 =>
      rw [SMT.Nat.two_pow_succ_sub_succ_div_two, ih]
      · simp [Nat.succ_lt_succ_iff]
      · omega

@[simp] theorem testBit_two_pow_sub_one (n i : Nat) : testBit (2^n-1) i = decide (i < n) := by
  rw [testBit_two_pow_sub_succ]
  · simp
  · exact Nat.two_pow_pos _

@[grind =]
theorem testBit_bool_toNat (b : Bool) (i : Nat) :
    testBit (Bool.toNat b) i = (decide (i = 0) && b) := by
  cases b <;> cases i <;>
  simp [testBit_eq_decide_div_mod_eq,
        Nat.mod_eq_of_lt]

/-- `testBit 1 i` is true iff the index `i` equals 0. -/
theorem testBit_one_eq_true_iff_self_eq_zero {i : Nat} :
    Nat.testBit 1 i = true ↔ i = 0 := by
  cases i <;> simp

@[grind =]
theorem testBit_two_pow {n m : Nat} : testBit (2 ^ n) m = decide (n = m) := by
  rw [testBit, shiftRight_eq_div_pow]
  by_cases h : n = m
  · simp [h, Nat.div_self (Nat.pow_pos Nat.zero_lt_two)]
  · simp only [h]
    cases Nat.lt_or_lt_of_ne h
    · rw [div_eq_of_lt (Nat.pow_lt_pow_of_lt (by omega) (by omega))]
      simp
    · rw [Nat.pow_div _ Nat.two_pos,
         ← Nat.sub_add_cancel (succ_le_of_lt <| Nat.sub_pos_of_lt (by omega))]
      simp [Nat.pow_succ, mul_mod_left]
      omega

@[simp]
theorem testBit_two_pow_self {n : Nat} : testBit (2 ^ n) n = true := by
  simp only [testBit_two_pow, decide_true]

@[simp]
theorem testBit_two_pow_of_ne {n m : Nat} (hm : n ≠ m) : testBit (2 ^ n) m = false := by
  simp only [testBit_two_pow, hm, decide_false]

@[simp] theorem two_pow_sub_one_mod_two : (2 ^ n - 1) % 2 = 1 % 2 ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [mod_eq_of_lt (a := 1) (Nat.one_lt_two_pow (by omega)), mod_two_eq_one_iff_testBit_zero, testBit_two_pow_sub_one ]
    simp only [zero_lt_succ, decide_true]

@[simp] theorem mod_two_pos_mod_two_eq_one : x % 2 ^ j % 2 = 1 ↔ (0 < j) ∧ x % 2 = 1 := by
  rw [mod_two_eq_one_iff_testBit_zero, testBit_mod_two_pow]
  simp


end SMT.Nat
