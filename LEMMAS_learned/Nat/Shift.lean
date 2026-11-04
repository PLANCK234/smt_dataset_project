/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local derivations from Lean 4.34.1 Init and the SMT API.
Source dependencies and pinned revisions: upstream.json.
-/
module
prelude

public import Init.ByCases
public import Init.Data.Nat.Div.Lemmas
public import Init.Data.Nat.Lemmas
public import Init.Omega
public import Init.RCases

@[expose] public section

namespace Learned.Nat

/-- A positive value below a power-of-two width cannot self-shift entirely out of the word. -/
theorem not_two_pow_dvd_self_shift_of_pow_width (k a : Nat) (ha : 0 < a) (hn : a < 2 ^ k) :
    ¬ 2 ^ (2 ^ k) ∣ a * 2 ^ a := by
  intro h
  let d := 2 ^ k - a
  have hd0 : 0 < d := by dsimp [d]; omega
  have had : a + d = 2 ^ k := by dsimp [d]; omega
  have hp : 2 ^ (2 ^ k) = 2 ^ d * 2 ^ a := by rw [← Nat.pow_add]; congr 1; omega
  rw [hp] at h
  have hd : 2 ^ d ∣ a := Nat.dvd_of_mul_dvd_mul_right (Nat.two_pow_pos a) h
  by_cases hdk : d ≤ k
  · have hdN : 2 ^ d ∣ 2 ^ k := Nat.pow_dvd_pow 2 hdk
    have hdd : 2 ^ d ∣ d := by
      dsimp [d]
      exact Nat.dvd_sub hdN hd
    have hle := Nat.le_of_dvd hd0 hdd
    have hlt := Nat.lt_two_pow_self (n := d)
    omega
  · have hlt : 2 ^ k < 2 ^ d := Nat.pow_lt_pow_right (by decide) (by omega)
    have hle := Nat.le_of_dvd ha hd
    omega

end Learned.Nat
