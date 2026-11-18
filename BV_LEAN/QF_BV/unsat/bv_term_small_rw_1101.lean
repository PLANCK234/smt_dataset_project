/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1101.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.ExactConditions
import LEMMAS_learned.BitVec.Shift.Conditions
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

def bv_term_small_rw_1101 : Prop :=
    ∀ (n : Nat) (s t : BitVec n),
      (bvand t (bvlshr s (bvshl s t))) = (bvand s (bvlshr t (bvshl s t)))

theorem bv_term_small_rw_1101_counterexample : ¬ bv_term_small_rw_1101 := by
  intro h
  have hbad : ¬ ((bvand (literal 3 1) (bvlshr (literal 3 5) (bvshl (literal 3 5) (literal 3 1)))) = (bvand (literal 3 5) (bvlshr (literal 3 1) (bvshl (literal 3 5) (literal 3 1))))) := by decide
  exact hbad (h 3 (literal 3 5) (literal 3 1))

theorem bv_term_small_rw_1101_restricted
    (n : Nat) (s t : BitVec n)
    (h : 2 ^ n ∣ s.toNat * 2 ^ t.toNat ∨ s.toNat * 2 ^ t.toNat < 2 ^ n) :
    (bvand t (bvlshr s (bvshl s t))) = (bvand s (bvlshr t (bvshl s t))) := by
  by_cases hb : bvshl s t = literal n 0
  · rw [hb]
    simp only [bvlshr_zero]
    exact bvand_comm _ _
  · have hp : s.toNat * 2 ^ t.toNat < 2 ^ n := h.resolve_left (fun hd => hb ((bvshl_eq_zero_iff_dvd s t).mpr hd))
    have hx := toNat_le_bvshl_of_mul_lt s t hp
    have hy := Nat.le_of_lt (lt_toNat_bvshl_of_ne_zero t s hb)
    have hs : bvlshr s (bvshl s t) = literal n 0 := bvlshr_eq_zero_of_le _ _ hx
    have ht : bvlshr t (bvshl s t) = literal n 0 := bvlshr_eq_zero_of_le _ _ hy
    rw [hs, ht, bvand_zero, bvand_zero]

/- WIDTH COROLLARY (2026-11-04). -/

theorem bv_term_small_rw_1101_width_restricted
    (n : Nat) (s t : BitVec n)
    (h : n = 0 ∨ ∃ k : Nat, n = 2 ^ k) :
    (bvand t (bvlshr s (bvshl s t))) = (bvand s (bvlshr t (bvshl s t))) := by
  rcases h with hn0 | ⟨k, hw⟩
  · subst n; exact Subsingleton.elim _ _
  ·
    by_cases hb : bvshl s t = literal n 0
    · rw [hb]
      simp only [bvlshr_zero]; exact bvand_comm _ _
    · have hy : bvlshr t (bvshl s t) = literal n 0 :=
        bvlshr_eq_zero_of_le _ _ (Nat.le_of_lt (lt_toNat_bvshl_of_ne_zero t s hb))
      have hz := bvand_bvshl_bvshl_swap_of_pow_width n k hw s t hb
      have hr : bvand t (bvlshr s (bvshl s t)) = literal n 0 := by
        rw [bvand_bvlshr_eq_bvlshr_bvand_bvshl, hz]
        simp [bvlshr, literal]
      rw [hr, hy, bvand_zero]

/- Analysis:
If b=s<<t is nonzero the right side is zero, so the condition is that the left mask is empty; the criteria are those of 458.
Exact conditions: `_iff` per input, `_width_iff` per width; see ../EXACT_CONDITIONS.md.
-/

theorem bv_term_small_rw_1101_iff (n : Nat) (s t : BitVec n) :
    ((bvand t (bvlshr s (bvshl s t))) = (bvand s (bvlshr t (bvshl s t)))) ↔
      CrossAdmissible n s.toNat t.toNat := by
  have hc : CrossAdmissible n s.toNat t.toNat ↔
      bvshl s t = literal n 0 ∨ bvand t (bvlshr s (bvshl s t)) = literal n 0 := by
    simp only [CrossAdmissible, eq_iff_toNat_eq, toNat_bvshl, toNat_bvand, toNat_bvlshr,
      toNat_literal, Nat.zero_mod]
  rw [hc]
  by_cases hb : bvshl s t = literal n 0
  · rw [hb]
    simp [bvand_comm]
  · have hy : bvlshr t (bvshl s t) = literal n 0 :=
      bvlshr_eq_zero_of_le _ _ (Nat.le_of_lt (lt_toNat_bvshl_of_ne_zero t s hb))
    simp only [hb, false_or]
    rw [hy, bvand_zero]

theorem bv_term_small_rw_1101_width_iff (n : Nat) :
    (∀ s t : BitVec n, (bvand t (bvlshr s (bvshl s t))) = (bvand s (bvlshr t (bvshl s t)))) ↔
      CrossWidth n := by
  have hpoint : (∀ s t : BitVec n, (bvand t (bvlshr s (bvshl s t))) = (bvand s (bvlshr t (bvshl s t)))) ↔
      ∀ s t : BitVec n, CrossAdmissible n s.toNat t.toNat := by
    constructor
    · intro h s t; exact (bv_term_small_rw_1101_iff n s t).mp (h s t)
    · intro h s t; exact (bv_term_small_rw_1101_iff n s t).mpr (h s t)
  rw [hpoint]
  rw [forall_bitvec_toNat_iff (n := n) (fun a d => CrossAdmissible n a d)]
  rfl

end BV.QF_BV.Unsat
