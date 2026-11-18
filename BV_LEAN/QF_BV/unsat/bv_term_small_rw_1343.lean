/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1343.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.ExactConditions
import LEMMAS_learned.BitVec.Shift.Conditions
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

def bv_term_small_rw_1343 : Prop :=
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvand s t) (bvshl t s)) = (bvand s (bvlshr t (bvshl t s)))

theorem bv_term_small_rw_1343_counterexample : ¬ bv_term_small_rw_1343 := by
  intro h
  have hbad : ¬ ((bvlshr (bvand (literal 3 1) (literal 3 5)) (bvshl (literal 3 5) (literal 3 1))) = (bvand (literal 3 1) (bvlshr (literal 3 5) (bvshl (literal 3 5) (literal 3 1))))) := by decide
  exact hbad (h 3 (literal 3 1) (literal 3 5))

theorem bv_term_small_rw_1343_restricted
    (n : Nat) (s t : BitVec n)
    (h : 2 ^ n ∣ t.toNat * 2 ^ s.toNat ∨ t.toNat * 2 ^ s.toNat < 2 ^ n) :
    (bvlshr (bvand s t) (bvshl t s)) = (bvand s (bvlshr t (bvshl t s))) := by
  by_cases hb : bvshl t s = literal n 0
  · rw [hb]
    simp only [bvlshr_zero]

  · have hp : t.toNat * 2 ^ s.toNat < 2 ^ n := h.resolve_left (fun hd => hb ((bvshl_eq_zero_iff_dvd t s).mpr hd))
    have hx := toNat_le_bvshl_of_mul_lt t s hp
    have hy := Nat.le_of_lt (lt_toNat_bvshl_of_ne_zero s t hb)
    have hs : bvlshr s (bvshl t s) = literal n 0 := bvlshr_eq_zero_of_le _ _ hy
    have ht : bvlshr t (bvshl t s) = literal n 0 := bvlshr_eq_zero_of_le _ _ hx
    rw [bvlshr_bvand, hs, ht, bvand_zero, bvand_zero]

/- WIDTH COROLLARY (2026-11-04). -/

theorem bv_term_small_rw_1343_width_restricted
    (n : Nat) (s t : BitVec n)
    (h : n = 0 ∨ ∃ k : Nat, n = 2 ^ k) :
    (bvlshr (bvand s t) (bvshl t s)) = (bvand s (bvlshr t (bvshl t s))) := by
  rcases h with hn0 | ⟨k, hw⟩
  · subst n; exact Subsingleton.elim _ _
  ·
    by_cases hb : bvshl t s = literal n 0
    · rw [hb]
      simp only [bvlshr_zero]
    · have hy : bvlshr s (bvshl t s) = literal n 0 :=
        bvlshr_eq_zero_of_le _ _ (Nat.le_of_lt (lt_toNat_bvshl_of_ne_zero s t hb))
      have hz := bvand_bvshl_bvshl_swap_of_pow_width n k hw t s hb
      have hr : bvand s (bvlshr t (bvshl t s)) = literal n 0 := by
        rw [bvand_bvlshr_eq_bvlshr_bvand_bvshl, hz]
        simp [bvlshr, literal]
      rw [bvlshr_bvand, hy, bvand_comm, bvand_zero, hr]

/- Analysis:
If b=t<<s is nonzero then s>>b=0 and the left side is zero; the exact condition is that of 473.
Exact conditions: `_iff` per input, `_width_iff` per width; see ../EXACT_CONDITIONS.md.
-/

theorem bv_term_small_rw_1343_iff (n : Nat) (s t : BitVec n) :
    ((bvlshr (bvand s t) (bvshl t s)) = (bvand s (bvlshr t (bvshl t s)))) ↔
      CrossAdmissible n t.toNat s.toNat := by
  have hc : CrossAdmissible n t.toNat s.toNat ↔
      bvshl t s = literal n 0 ∨ bvand s (bvlshr t (bvshl t s)) = literal n 0 := by
    simp only [CrossAdmissible, eq_iff_toNat_eq, toNat_bvshl, toNat_bvand, toNat_bvlshr,
      toNat_literal, Nat.zero_mod]
  rw [hc]
  by_cases hb : bvshl t s = literal n 0
  · rw [hb]
    simp
  · have hy : bvlshr s (bvshl t s) = literal n 0 :=
      bvlshr_eq_zero_of_le _ _ (Nat.le_of_lt (lt_toNat_bvshl_of_ne_zero s t hb))
    simp only [hb, false_or]
    rw [bvlshr_bvand, hy, bvand_comm (literal n 0), bvand_zero, eq_comm (a := literal n 0)]

theorem bv_term_small_rw_1343_width_iff (n : Nat) :
    (∀ s t : BitVec n, (bvlshr (bvand s t) (bvshl t s)) = (bvand s (bvlshr t (bvshl t s)))) ↔
      CrossWidth n := by
  have hpoint : (∀ s t : BitVec n, (bvlshr (bvand s t) (bvshl t s)) = (bvand s (bvlshr t (bvshl t s)))) ↔
      ∀ s t : BitVec n, CrossAdmissible n t.toNat s.toNat := by
    constructor
    · intro h s t; exact (bv_term_small_rw_1343_iff n s t).mp (h s t)
    · intro h s t; exact (bv_term_small_rw_1343_iff n s t).mpr (h s t)
  rw [hpoint]
  rw [forall_bitvec_toNat_iff (n := n) (fun a d => CrossAdmissible n d a)]
  constructor
  · intro h x hx y hy; exact h y hy x hx
  · intro h a ha d hd; exact h d hd a ha

end BV.QF_BV.Unsat
