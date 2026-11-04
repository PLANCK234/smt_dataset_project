import LEMMAS_learned.BitVec.Shift.Characterization
import LEMMAS_learned.BitVec.Shift.Conditions

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

/-- Exact bit-pattern condition for equality of left and right shifts by q. -/
def ShiftBalanced (n a q : Nat) : Prop :=
  2 ^ (n + q) ∣ (2 ^ (q + q) - 1) * a + a % 2 ^ q

/-- Excludes exactly the single-top-bit inner result, not all overflow. -/
def ComplementAdmissible (n a : Nat) : Prop :=
  (a * 2 ^ (2 ^ n - 1 - a)) % 2 ^ n ≠ 2 ^ (n - 1)

/-- Exact self-shift condition for the all-ones comparison. -/
def SelfShiftAdmissible (n a : Nat) : Prop :=
  a = 0 ∨ n ≤ a ∨ ¬ 2 ^ n ∣ a * 2 ^ a

/-- With b = x*2^y mod 2^n, no bit of y may meet the corresponding bit of x above b.
The b=0 branch is always valid. This is an exact input condition, allowing overflow. -/
def CrossAdmissible (n x y : Nat) : Prop :=
  (x * 2 ^ y) % 2 ^ n = 0 ∨ y &&& (x / 2 ^ ((x * 2 ^ y) % 2 ^ n)) = 0


/-- Arithmetic characterization of the admissible widths for 296/298/379/380. -/
def ComplementWidth (n : Nat) : Prop := ∀ a, a < 2 ^ n → ComplementAdmissible n a

/-- No positive self-shift below the width is completely truncated. -/
def SelfShiftWidth (n : Nat) : Prop :=
  ∀ a, 0 < a → a < n → ¬ 2 ^ n ∣ a * 2 ^ a

/-- Exact arithmetic width condition for the four crossed-mask identities.
EXACT_CONDITIONS.md eliminates the x quantifier and reduces this to bits of y and n % 2^y. -/
def CrossWidth (n : Nat) : Prop :=
  ∀ x, x < 2 ^ n → ∀ y, y < 2 ^ n → CrossAdmissible n x y

/-- Only small square residues can create a nonzero, nonclearing effective count. -/
def SquareWidth301 (n : Nat) : Prop :=
  ∀ r, r < n → ∀ a, a < 2 ^ n → a * a % 2 ^ n = r → ShiftBalanced n a (a / 2 ^ r)

def SquareWidth477 (n : Nat) : Prop :=
  ∀ r, r < n → ∀ a, a < 2 ^ n → a * a % 2 ^ n = r →
    a < 2 ^ r ∨ n * 2 ^ r ≤ a

theorem forall_bitvec_toNat_iff (F : Nat → Nat → Prop) :
    (∀ s t : BitVec n, F s.toNat t.toNat) ↔ ∀ a, a < 2 ^ n → ∀ d, d < 2 ^ n → F a d := by
  constructor
  · intro h a ha d hd
    simpa only [toNat_literal, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hd] using h (literal n a) (literal n d)
  · intro h s t
    exact h s.toNat s.isLt t.toNat t.isLt

theorem selfShiftWidth_iff : SelfShiftWidth n ↔ ∀ a, a < 2 ^ n → SelfShiftAdmissible n a := by
  constructor
  · intro h a ha
    by_cases hz : a = 0
    · exact Or.inl hz
    by_cases hn : n ≤ a
    · exact Or.inr (Or.inl hn)
    exact Or.inr (Or.inr (h a (by omega) (by omega)))
  · intro h a ha hn
    have hp := Nat.lt_two_pow_self (n := n)
    have hc := h a (by omega)
    rcases hc with h | h | h
    · omega
    · omega
    · exact h

theorem shiftBalanced_zero (n a : Nat) : ShiftBalanced n a 0 := by
  simp [ShiftBalanced, Nat.mod_one]

theorem forall_shiftBalanced_iff (hq : q < 2 ^ n) :
    (∀ a, a < 2 ^ n → ShiftBalanced n a q) ↔ q = 0 ∨ n ≤ q := by
  have hv : (literal n q).toNat = q := by rw [toNat_literal, Nat.mod_eq_of_lt hq]
  constructor
  · intro h
    have he : ∀ x : BitVec n, bvshl x (literal n q) = bvlshr x (literal n q) := by
      intro x
      apply (bvshl_eq_bvlshr_iff_dvd _ _).mpr
      simpa only [ShiftBalanced, hv] using h x.toNat x.isLt
    simpa only [hv] using (bvshl_eq_bvlshr_forall_iff _).mp he
  · intro h a ha
    have he := (bvshl_eq_bvlshr_forall_iff (literal n q)).mpr (by simpa only [hv] using h) (literal n a)
    have hh := (bvshl_eq_bvlshr_iff_dvd _ _).mp he
    simpa only [ShiftBalanced, toNat_literal, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hq] using hh

end BV.QF_BV.Unsat
