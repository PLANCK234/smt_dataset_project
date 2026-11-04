/-
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Local derivations from Lean 4.34.1 Init and the SMT API.
Source dependencies and pinned revisions: upstream.json.
-/
module
prelude

public import SMT.Nat.Order

@[expose] public section

namespace Learned.Nat
open SMT.Nat

/-- Disjoint binary digits add without carrying. -/
theorem or_eq_add_of_and_eq_zero {a b : Nat} (h : a &&& b = 0) : a ||| b = a + b := by
  induction a using SMT.Nat.div2Induction generalizing b with
  | ind a ih =>
    by_cases ha : a = 0
    · subst a; simp
    have hab : a / 2 &&& b / 2 = 0 := by
      rw [← SMT.Nat.and_div_two, h]
    have hid := ih (by omega) hab
    have hor : (a ||| b) / 2 = a / 2 ||| b / 2 := SMT.Nat.or_div_two
    rw [hid] at hor
    have ham : a % 2 &&& b % 2 = 0 := by
      rw [← SMT.Nat.and_mod_two_pow (n := 1)]
      simp [h]
    have hom : (a ||| b) % 2 = a % 2 ||| b % 2 := SMT.Nat.or_mod_two_pow (n := 1)
    have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2 <;>
      simp only [ha2, hb2, SMT.Nat.zero_and, SMT.Nat.and_zero, SMT.Nat.and_self,
        SMT.Nat.zero_or, SMT.Nat.or_zero, SMT.Nat.or_self] at ham hom <;> omega

/-- A mask below 2^k sees only the lowest k bits of either operand. -/
theorem and_eq_of_mod_two_pow_eq {a b c k : Nat} (ha : a < 2 ^ k)
    (h : b % 2 ^ k = c % 2 ^ k) : a &&& b = a &&& c := by
  calc
    a &&& b = (a &&& b) % 2 ^ k := (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt SMT.Nat.and_le_left ha)).symm
    _ = (a % 2 ^ k) &&& (c % 2 ^ k) := by rw [SMT.Nat.and_mod_two_pow, h]
    _ = a &&& c := by
      rw [← SMT.Nat.and_mod_two_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt SMT.Nat.and_le_left ha)]

end Learned.Nat
