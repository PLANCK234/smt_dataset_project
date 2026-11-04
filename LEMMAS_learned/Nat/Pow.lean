/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local derivations from Lean 4.34.1 Init and the SMT API.
Source dependencies and pinned revisions: upstream.json.
-/
module
prelude

public import Init.ByCases
public import Init.Data.Int.Pow
public import Init.Data.Nat.Lemmas
public import Init.Omega
public import Init.RCases

@[expose] public section

namespace Learned.Nat

theorem two_mul_le_two_pow : 2 * n ≤ 2 ^ n := by
  cases n with
  | zero => decide
  | succ k =>
    have h : k < 2 ^ k := Nat.lt_two_pow_self
    rw [Nat.pow_succ]
    omega

theorem sq_lt_two_pow_succ (a : Nat) : a * a < 2 ^ (a + 1) := by
  induction a with
  | zero => decide
  | succ a ih =>
    match a with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | b + 3 =>
      have hmul : 3 * (b + 3) ≤ (b + 3) * (b + 3) := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.pow_succ 2 (b + 3 + 1)]
      rw [Nat.add_mul, Nat.mul_add]
      simp only [Nat.one_mul, Nat.mul_one]
      simp only [Nat.add_assoc] at ih ⊢
      omega

theorem two_mul_lt_two_pow_of_three_le (a : Nat) (h : 3 ≤ a) : 2 * a < 2 ^ a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 3 + (k + 1) = (3 + k) + 1 by omega, Nat.pow_succ]
    omega

theorem succ_lt_two_pow_of_two_le (a : Nat) (h : 2 ≤ a) : a + 1 < 2 ^ a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 2 + (k + 1) = (2 + k) + 1 by omega, Nat.pow_succ]
    omega

theorem sq_lt_two_pow_double (a : Nat) : a * a < 2 ^ (a + a) := by
  by_cases h : a = 0
  · subst a; decide
  · exact Nat.lt_of_lt_of_le (Learned.Nat.sq_lt_two_pow_succ a)
      (Nat.pow_le_pow_right (by decide) (by omega))

end Learned.Nat
