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
public import Init.Data.Nat.MinMax
public import Init.Omega
public import Init.RCases

@[expose] public section

namespace Learned.Nat

theorem add_div_two_pow_le_max (a b : Nat) : b + a / 2^b ≤ max a b := by
  by_cases h : a / 2^b = 0
  · simp only [h, Nat.add_zero]; exact Nat.le_max_right _ _
  · have hq : 1 ≤ a / 2^b := Nat.pos_of_ne_zero h
    apply Nat.le_trans (m := a)
    · calc
        b + a / 2^b ≤ (a / 2^b) * b + a / 2^b := by
          have hb := Nat.mul_le_mul_right b hq
          simp only [Nat.one_mul] at hb
          omega
        _ = (a / 2^b) * (b+1) := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ (a / 2^b) * 2^b := Nat.mul_le_mul_left _ Nat.lt_two_pow_self
        _ ≤ a := Nat.div_mul_le_self _ _
    · exact Nat.le_max_left _ _

theorem lt_two_pow_add_div (a b : Nat) : a < 2^(b + a / 2^b) := by
  have hd : a < (a / 2^b + 1) * 2^b := by
    have hm := Nat.mod_lt a (Nat.two_pow_pos b)
    have ha := Nat.div_add_mod a (2^b)
    rw [Nat.mul_comm (2^b)] at ha
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    a < (a / 2^b + 1) * 2^b := hd
    _ ≤ 2^(a / 2^b) * 2^b := Nat.mul_le_mul_right _ Nat.lt_two_pow_self
    _ = 2^(b + a / 2^b) := by rw [Nat.pow_add, Nat.mul_comm]

theorem sub_div_eq_pred_of_dvd {p d a : Nat} (hd : d ∣ p)
    (ha : 0 < a) (had : a ≤ d) (hap : a ≤ p) :
    (p - a) / d = p / d - 1 := by
  obtain ⟨k, hk⟩ := hd
  rw [hk]
  rw [show d * k - a = d * k - (a - 1 + 1) by omega,
    Nat.mul_sub_div _ _ _ (by omega), Nat.div_eq_of_lt (by omega)]
  simp [Nat.mul_div_right, show 0 < d by omega]

end Learned.Nat
