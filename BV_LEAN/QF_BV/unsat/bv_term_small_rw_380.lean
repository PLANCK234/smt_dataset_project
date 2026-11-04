/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_380.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.ExactConditions
import LEMMAS_learned.BitVec.Shift.Characterization
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

def bv_term_small_rw_380 : Prop :=
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvshl t (bvnot t))) = (bvlshr s (bvshl t (bvneg t)))

theorem bv_term_small_rw_380_counterexample : ¬ bv_term_small_rw_380 := by
  intro h
  have hbad : ¬ ((bvshl (literal 1 1) (bvshl (literal 1 1) (bvnot (literal 1 1)))) = (bvlshr (literal 1 1) (bvshl (literal 1 1) (bvneg (literal 1 1))))) := by decide
  exact hbad (h 1 (literal 1 1) (literal 1 1))

theorem bv_term_small_rw_380_restricted
    (n : Nat) (s t : BitVec n)
    (h : (t.toNat * 2 ^ (2 ^ n - 1 - t.toNat)) % 2 ^ n ≠ 2 ^ (n - 1)) :
    (bvshl s (bvshl t (bvnot t))) = (bvlshr s (bvshl t (bvneg t))) := by
  have hh : (bvshl t (bvnot t)).toNat ≠ 2 ^ (n - 1) := by
    simpa only [toNat_bvshl, toNat_bvnot] using h
  have he := bvshl_bvnot_eq_zero_iff_bvshl_bvneg_eq_zero t hh
  by_cases ha : bvshl t (bvnot t) = literal n 0
  · rw [ha, he.mp ha]
    simp only [bvshl_zero, bvlshr_zero]
  · have hb := fun hb => ha (he.mpr hb)
    have hA := width_le_toNat_bvshl_bvnot_self (bvnot t) (by simpa only [bvnot_bvnot] using ha)
    simp only [bvnot_bvnot] at hA
    have hB := width_le_toNat_bvshl_bvneg_self t hb
    rw [bvshl_large _ _ hA, bvlshr_large _ _ hB]

/- WIDTH COROLLARY (2026-11-04). -/

theorem bv_term_small_rw_380_width_restricted
    (n : Nat) (s t : BitVec n)
    (h : n = 0 ∨ ∃ k : Nat, n = 2 ^ (k + 1)) :
    (bvshl s (bvshl t (bvnot t))) = (bvlshr s (bvshl t (bvneg t))) := by
  rcases h with hn0 | ⟨k, hw⟩
  · subst n; exact Subsingleton.elim _ _
  ·
    apply bv_term_small_rw_380_restricted n s t
    have hh := bvshl_bvnot_self_ne_top_of_pow_width n k hw t
    simpa only [toNat_bvshl, toNat_bvnot] using hh

/- 数学分析：
外层 s=0 总成立；s 非零时，充要条件是 t<<~t 不仅剩最高位。位宽统一条件同 296/298/379。
输入与全输入位宽的充要条件分别见 `_iff`、`_width_iff`。
进一步的位宽算术判据与待形式化部分见 ../EXACT_CONDITIONS.md。
-/

theorem bv_term_small_rw_380_iff (n : Nat) (s t : BitVec n) :
    ((bvshl s (bvshl t (bvnot t))) = (bvlshr s (bvshl t (bvneg t)))) ↔
      s.toNat = 0 ∨ ComplementAdmissible n t.toNat := by
  by_cases hs : s = literal n 0
  · subst s
    simp [bvshl_eq_shiftLeft, bvlshr, literal]
  have hsval : s.toNat ≠ 0 := by
    intro h; apply hs; apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using h
  simp only [hsval, false_or]
  by_cases hh : ComplementAdmissible n t.toNat
  · exact iff_of_true (bv_term_small_rw_380_restricted n s t hh) hh
  · have htop : (bvshl t (bvnot t)).toNat = 2 ^ (n - 1) := by
      simp only [ComplementAdmissible] at hh
      rw [toNat_bvshl, toNat_bvnot]; omega
    obtain ⟨hA, hB, hx⟩ := bvshl_bvnot_self_top_obstruction t htop
    rw [bvshl_large _ _ hA, hB, bvlshr_zero]
    constructor
    · intro he; exact False.elim (hs he.symm)
    · intro he; exact False.elim (hh he)

theorem bv_term_small_rw_380_width_iff (n : Nat) :
    (∀ s t : BitVec n, (bvshl s (bvshl t (bvnot t))) = (bvlshr s (bvshl t (bvneg t)))) ↔
      ComplementWidth n := by
  have hpoint : (∀ s t : BitVec n, (bvshl s (bvshl t (bvnot t))) = (bvlshr s (bvshl t (bvneg t)))) ↔
      ∀ s t : BitVec n, s.toNat = 0 ∨ ComplementAdmissible n t.toNat := by
    constructor
    · intro h s t; exact (bv_term_small_rw_380_iff n s t).mp (h s t)
    · intro h s t; exact (bv_term_small_rw_380_iff n s t).mpr (h s t)
  rw [hpoint]
  rw [forall_bitvec_toNat_iff (n := n) (fun a d => a = 0 ∨ ComplementAdmissible n d)]
  constructor
  · intro h d hd
    by_cases hp : 1 < 2 ^ n
    · have hc := h 1 hp d hd
      exact hc.resolve_left (by decide)
    · have hpos := Nat.two_pow_pos n
      have hd0 : d = 0 := by omega
      rw [hd0]
      unfold ComplementAdmissible
      simp only [Nat.zero_mul, Nat.zero_mod]
      exact Nat.ne_of_lt (Nat.two_pow_pos _)
  · intro h a ha d hd
    exact Or.inr (h d hd)

end BV.QF_BV.Unsat
