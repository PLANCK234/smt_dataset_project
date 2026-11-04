/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local derivations from Lean 4.34.1 Init and the SMT API.
Source dependencies and pinned revisions: upstream.json.
-/
module
prelude

public import Init.Data.Nat.Lemmas
public import Init.Data.Nat.Div.Lemmas
public import Init.Omega
public import Init.RCases

@[expose] public section

namespace Learned.Nat

/-- A specified remainder is equivalent to divisibility after subtracting it. -/
theorem mod_eq_iff_dvd_sub_of_le {x m r : Nat} (hr : r < m) (hle : r ≤ x) :
    x % m = r ↔ m ∣ x - r := by
  constructor
  · intro h
    rcases Nat.mod_eq_iff.mp h with h | ⟨_, k, hk⟩
    · omega
    · exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    apply Nat.mod_eq_iff.mpr
    exact Or.inr ⟨hr, k, by omega⟩

end Learned.Nat
