/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_522.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.ExactConditions
import LEMMAS_learned.BitVec.Shift.Characterization
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

def bv_term_small_rw_522 : Prop :=
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvlshr t (bvshl t t))) = (bvlshr s (bvlshr t (bvshl t t)))

theorem bv_term_small_rw_522_counterexample : ¬ bv_term_small_rw_522 := by
  intro h
  have hbad : ¬ ((bvshl (literal 3 1) (bvlshr (literal 3 2) (bvshl (literal 3 2) (literal 3 2)))) = (bvlshr (literal 3 1) (bvlshr (literal 3 2) (bvshl (literal 3 2) (literal 3 2))))) := by decide
  exact hbad (h 3 (literal 3 1) (literal 3 2))

theorem bv_term_small_rw_522_restricted
    (n : Nat) (s t : BitVec n)
    (h : t.toNat = 0 ∨ n ≤ t.toNat ∨ ¬ 2 ^ n ∣ t.toNat * 2 ^ t.toNat) :
    (bvshl s (bvlshr t (bvshl t t))) = (bvlshr s (bvlshr t (bvshl t t))) := by
  rcases h with hz | hn | hd
  · have ht : t = literal n 0 := by
      apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using hz
    subst t; simp [bvshl_eq_shiftLeft, bvlshr, literal]
  · rw [bvshl_large _ _ hn, bvlshr_zero, bvshl_large _ _ hn, bvlshr_large _ _ hn]
  · have hb : bvshl t t ≠ literal n 0 := fun hb => hd ((bvshl_eq_zero_iff_dvd t t).mp hb)
    rw [bvlshr_bvshl_self_eq_ite, ite_eq_right hb, bvshl_zero, bvlshr_zero]

/- WIDTH COROLLARY (2026-11-04). -/

theorem bv_term_small_rw_522_width_restricted
    (n : Nat) (s t : BitVec n)
    (h : n = 0 ∨ ∃ k : Nat, n = 2 ^ k) :
    (bvshl s (bvlshr t (bvshl t t))) = (bvlshr s (bvlshr t (bvshl t t))) := by
  rcases h with hn0 | ⟨k, hw⟩
  · subst n; exact Subsingleton.elim _ _
  ·
    apply bv_term_small_rw_522_restricted n s t
    by_cases hz : t.toNat = 0
    · exact Or.inl hz
    by_cases hn : n ≤ t.toNat
    · exact Or.inr (Or.inl hn)
    apply Or.inr ∘ Or.inr
    have hlt : t.toNat < 2 ^ k := by omega
    have hd := Learned.Nat.not_two_pow_dvd_self_shift_of_pow_width k t.toNat (by omega) hlt
    simpa only [show 2 ^ n = 2 ^ (2 ^ k) by rw [hw]] using hd

/- Analysis:
If t<<t is nonzero the effective count is zero; otherwise the exact condition is ShiftBalanced(n,s,t). Over all s, this excludes exactly 0<t<n with a zero self-shift.
Exact conditions: `_iff` per input, `_width_iff` per width; see ../EXACT_CONDITIONS.md.
-/

theorem bv_term_small_rw_522_iff (n : Nat) (s t : BitVec n) :
    ((bvshl s (bvlshr t (bvshl t t))) = (bvlshr s (bvlshr t (bvshl t t)))) ↔
      ¬ 2 ^ n ∣ t.toNat * 2 ^ t.toNat ∨ ShiftBalanced n s.toNat t.toNat := by
  by_cases hb : bvshl t t = literal n 0
  · have hd := (bvshl_eq_zero_iff_dvd t t).mp hb
    rw [bvlshr_bvshl_self_eq_ite, ite_eq_left hb]
    simp only [hd, not_true_eq_false, false_or]
    exact bvshl_eq_bvlshr_iff_dvd s t
  · have hd : ¬ 2 ^ n ∣ t.toNat * 2 ^ t.toNat := fun h => hb ((bvshl_eq_zero_iff_dvd t t).mpr h)
    rw [bvlshr_bvshl_self_eq_ite, ite_eq_right hb, bvshl_zero, bvlshr_zero]
    exact iff_of_true rfl (Or.inl hd)

theorem bv_term_small_rw_522_width_iff (n : Nat) :
    (∀ s t : BitVec n, (bvshl s (bvlshr t (bvshl t t))) = (bvlshr s (bvlshr t (bvshl t t)))) ↔
      SelfShiftWidth n := by
  have hpoint : (∀ s t : BitVec n, (bvshl s (bvlshr t (bvshl t t))) = (bvlshr s (bvlshr t (bvshl t t)))) ↔
      ∀ s t : BitVec n, ¬ 2 ^ n ∣ t.toNat * 2 ^ t.toNat ∨ ShiftBalanced n s.toNat t.toNat := by
    constructor
    · intro h s t; exact (bv_term_small_rw_522_iff n s t).mp (h s t)
    · intro h s t; exact (bv_term_small_rw_522_iff n s t).mpr (h s t)
  rw [hpoint]
  rw [forall_bitvec_toNat_iff (n := n) (fun a d => ¬ 2 ^ n ∣ d * 2 ^ d ∨ ShiftBalanced n a d)]
  constructor
  · intro h d hpos hn hd
    have hdp : d < 2 ^ n := Nat.lt_trans hn Nat.lt_two_pow_self
    have he : ∀ a, a < 2 ^ n → ShiftBalanced n a d := by
      intro a ha
      exact (h a ha d hdp).resolve_left (by intro h; exact h hd)
    have hc := (forall_shiftBalanced_iff hdp).mp he
    omega
  · intro h a ha d hd
    by_cases hdiv : 2 ^ n ∣ d * 2 ^ d
    · have hc := selfShiftWidth_iff.mp h d hd
      have hz : d = 0 ∨ n ≤ d := by
        rcases hc with hc | hc | hc
        · exact Or.inl hc
        · exact Or.inr hc
        · exact False.elim (hc hdiv)
      exact Or.inr ((forall_shiftBalanced_iff hd).mpr hz a ha)
    · exact Or.inl hdiv

end BV.QF_BV.Unsat
