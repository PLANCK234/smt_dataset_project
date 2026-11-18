/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_296.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.ExactConditions
import LEMMAS_learned.BitVec.Shift.Characterization
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

def bv_term_small_rw_296 : Prop :=
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvshl s (bvnot s))) = (bvlshr s (bvshl s (bvneg s)))

theorem bv_term_small_rw_296_counterexample : ¬ bv_term_small_rw_296 := by
  intro h
  have hbad : ¬ ((bvlshr (literal 1 1) (bvshl (literal 1 1) (bvnot (literal 1 1)))) = (bvlshr (literal 1 1) (bvshl (literal 1 1) (bvneg (literal 1 1))))) := by decide
  exact hbad (h 1 (literal 1 1) (literal 1 0))

theorem bv_term_small_rw_296_restricted
    (n : Nat) (s t : BitVec n)
    (h : (s.toNat * 2 ^ (2 ^ n - 1 - s.toNat)) % 2 ^ n ≠ 2 ^ (n - 1)) :
    (bvlshr s (bvshl s (bvnot s))) = (bvlshr s (bvshl s (bvneg s))) := by
  have hh : (bvshl s (bvnot s)).toNat ≠ 2 ^ (n - 1) := by
    simpa only [toNat_bvshl, toNat_bvnot] using h
  have he := bvshl_bvnot_eq_zero_iff_bvshl_bvneg_eq_zero s hh
  by_cases ha : bvshl s (bvnot s) = literal n 0
  · rw [ha, he.mp ha]
  · have hb := fun hb => ha (he.mpr hb)
    have hA := width_le_toNat_bvshl_bvnot_self (bvnot s) (by simpa only [bvnot_bvnot] using ha)
    simp only [bvnot_bvnot] at hA
    have hB := width_le_toNat_bvshl_bvneg_self s hb
    rw [bvlshr_large _ _ hA, bvlshr_large _ _ hB]

/- WIDTH COROLLARY (2026-11-04). -/

theorem bv_term_small_rw_296_width_restricted
    (n : Nat) (s t : BitVec n)
    (h : n = 0 ∨ ∃ k : Nat, n = 2 ^ (k + 1)) :
    (bvlshr s (bvshl s (bvnot s))) = (bvlshr s (bvshl s (bvneg s))) := by
  rcases h with hn0 | ⟨k, hw⟩
  · subst n; exact Subsingleton.elim _ _
  ·
    apply bv_term_small_rw_296_restricted n s t
    have hh := bvshl_bvnot_self_ne_top_of_pow_width n k hw s
    simpa only [toNat_bvshl, toNat_bvnot] using hh

/- Analysis:
Both inner counts are 0 or at least n, and the second is twice the first mod 2^n. The only failing pattern is the first count being just the top bit, which forces s≠0.
Exact conditions: `_iff` per input, `_width_iff` per width; see ../EXACT_CONDITIONS.md.
-/

theorem bv_term_small_rw_296_iff (n : Nat) (s t : BitVec n) :
    ((bvlshr s (bvshl s (bvnot s))) = (bvlshr s (bvshl s (bvneg s)))) ↔
      ComplementAdmissible n s.toNat := by
  by_cases hh : ComplementAdmissible n s.toNat
  · exact iff_of_true (bv_term_small_rw_296_restricted n s t hh) hh
  · have htop : (bvshl s (bvnot s)).toNat = 2 ^ (n - 1) := by
      simp only [ComplementAdmissible] at hh
      rw [toNat_bvshl, toNat_bvnot]; omega
    obtain ⟨hA, hB, hx⟩ := bvshl_bvnot_self_top_obstruction s htop
    rw [bvlshr_large _ _ hA, hB, bvlshr_zero]
    constructor
    · intro he; exact False.elim (hx he.symm)
    · intro he; exact False.elim (hh he)

theorem bv_term_small_rw_296_width_iff (n : Nat) :
    (∀ s t : BitVec n, (bvlshr s (bvshl s (bvnot s))) = (bvlshr s (bvshl s (bvneg s)))) ↔
      ComplementWidth n := by
  have hpoint : (∀ s t : BitVec n, (bvlshr s (bvshl s (bvnot s))) = (bvlshr s (bvshl s (bvneg s)))) ↔
      ∀ s t : BitVec n, ComplementAdmissible n s.toNat := by
    constructor
    · intro h s t; exact (bv_term_small_rw_296_iff n s t).mp (h s t)
    · intro h s t; exact (bv_term_small_rw_296_iff n s t).mpr (h s t)
  rw [hpoint]
  rw [forall_bitvec_toNat_iff (n := n) (fun a d => ComplementAdmissible n a)]
  constructor
  · intro h a ha
    exact h a ha 0 (Nat.two_pow_pos n)
  · intro h a ha d hd
    exact h a ha

end BV.QF_BV.Unsat
