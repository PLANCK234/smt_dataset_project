/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1246.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.ExactConditions
import Init.Data.Nat.MinMax
import LEMMAS_learned.Nat.Pow
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec

def bv_term_small_rw_1246 : Prop :=
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvmul s s) (bvadd s s)) = (literal n 0)

theorem bv_term_small_rw_1246_counterexample : ¬ bv_term_small_rw_1246 := by
  intro h
  have hbad : ¬ ((bvlshr (bvmul (literal 1 1) (literal 1 1)) (bvadd (literal 1 1) (literal 1 1))) = (literal 1 0)) := by decide
  exact hbad (h 1 (literal 1 1) (literal 1 0))

theorem bv_term_small_rw_1246_restricted
    (n : Nat) (s t : BitVec n)
    (h : n ≠ 1) :
    (bvlshr (bvmul s s) (bvadd s s)) = (literal n 0) := by
  by_cases hn0 : n = 0
  · subst n; exact Subsingleton.elim _ _
  have hn : 2 ≤ n := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hp : 2 ^ (2 + k) = 4 * 2 ^ k := by rw [Nat.pow_add]
  have hs := s.isLt
  apply toNat_injective
  simp only [toNat_bvlshr, toNat_bvmul, toNat_bvadd, toNat_literal, Nat.zero_mod]
  apply Nat.div_eq_of_lt
  by_cases hsmall : s.toNat < 2 * 2 ^ k
  · rw [Nat.mod_eq_of_lt (show s.toNat + s.toNat < 2 ^ (2 + k) by omega)]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Learned.Nat.sq_lt_two_pow_double s.toNat)
  · let a := s.toNat - 2 * 2 ^ k
    have he : s.toNat = a + 2 * 2 ^ k := by dsimp [a]; omega
    have ha : a < 2 * 2 ^ k := by omega
    have hd : (s.toNat + s.toNat) % 2 ^ (2 + k) = a + a := by
      rw [he, hp]
      have hsum : a + 2 * 2 ^ k + (a + 2 * 2 ^ k) = a + a + 4 * 2 ^ k := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hsquare : (s.toNat * s.toNat) % 2 ^ (2 + k) = (a * a) % 2 ^ (2 + k) := by
      have hexpand : (a + 2 * 2 ^ k) * (a + 2 * 2 ^ k) =
          a * a + (4 * 2 ^ k) * a + (4 * 2 ^ k) * 2 ^ k := by
        have hc : a * (2 * 2 ^ k) = 2 * (2 ^ k * a) := by ac_rfl
        have ht : (2 * 2 ^ k) * (2 * 2 ^ k) = 4 * (2 ^ k * 2 ^ k) := by
          calc
            _ = (2 * 2) * (2 ^ k * 2 ^ k) := by ac_rfl
            _ = _ := rfl
        simp only [Nat.add_mul, Nat.mul_add]
        rw [hc, ht]
        simp only [Nat.mul_assoc]
        omega
      rw [he, hp, hexpand, Nat.add_mod, Nat.mul_mod_right, Nat.add_zero,
        Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod, Nat.mod_mod]
    rw [hd, hsquare]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Learned.Nat.sq_lt_two_pow_double a)

/- Analysis:
For n>=2, dropping the top bit does not change the square mod 2^n, so the shifted doubled value is zero; the only bad input is n=1, s=1.
Exact conditions: `_iff` per input, `_width_iff` per width; see ../EXACT_CONDITIONS.md.
-/

theorem bv_term_small_rw_1246_iff (n : Nat) (s t : BitVec n) :
    ((bvlshr (bvmul s s) (bvadd s s)) = (literal n 0)) ↔
      n ≠ 1 ∨ s.toNat = 0 := by
  by_cases hn : n = 1
  · subst n
    have hs := s.isLt
    have ht := t.isLt
    have hsc : s.toNat = 0 ∨ s.toNat = 1 := by omega
    have htc : t.toNat = 0 ∨ t.toNat = 1 := by omega
    rcases hsc with hs0 | hs1 <;>
      rcases htc with ht0 | ht1 <;>
      simp_all [eq_iff_toNat_eq]
  exact iff_of_true (bv_term_small_rw_1246_restricted n s t hn) (Or.inl hn)

theorem bv_term_small_rw_1246_width_iff (n : Nat) :
    (∀ s t : BitVec n, (bvlshr (bvmul s s) (bvadd s s)) = (literal n 0)) ↔
      n ≠ 1 := by
  constructor
  · intro h hn
    subst n
    have hc := (bv_term_small_rw_1246_iff 1 (literal 1 1) (literal 1 0)).mp (h (literal 1 1) (literal 1 0))
    simp at hc
  · intro hn s t
    exact bv_term_small_rw_1246_restricted n s t hn

end BV.QF_BV.Unsat
