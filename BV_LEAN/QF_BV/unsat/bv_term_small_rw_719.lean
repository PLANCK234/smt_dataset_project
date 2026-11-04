/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_719.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.ExactConditions
import LEMMAS_learned.BitVec.Shift.Conditions
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (or_eq_zero_iff)

def bv_term_small_rw_719 : Prop :=
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvshl (bvor s t) s)) = (bvlshr s (bvshl s s))

theorem bv_term_small_rw_719_counterexample : ¬ bv_term_small_rw_719 := by
  intro h
  have hbad : ¬ ((bvlshr (literal 3 2) (bvshl (bvor (literal 3 2) (literal 3 1)) (literal 3 2))) = (bvlshr (literal 3 2) (bvshl (literal 3 2) (literal 3 2)))) := by decide
  exact hbad (h 3 (literal 3 2) (literal 3 1))

theorem bv_term_small_rw_719_restricted
    (n : Nat) (s t : BitVec n)
    (h : s.toNat = 0 ∨ n ≤ s.toNat ∨ ¬ 2 ^ n ∣ s.toNat * 2 ^ s.toNat) :
    (bvlshr s (bvshl (bvor s t) s)) = (bvlshr s (bvshl s s)) := by
  rcases h with hz | hn | hd
  · have hs : s = literal n 0 := by
      apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using hz
    subst s; simp [bvlshr, literal]
  · rw [bvshl_large _ _ hn, bvshl_large _ _ hn]
  · have hb : bvshl s s ≠ literal n 0 := fun hb => hd ((bvshl_eq_zero_iff_dvd s s).mp hb)
    have hc : bvshl (bvor s t) s ≠ literal n 0 := by
      rw [bvshl_bvor]
      intro he
      exact hb (or_eq_zero_iff.mp he).1
    rw [bvlshr_bvshl_self_eq_ite, ite_eq_right hc, bvlshr_bvshl_self_eq_ite, ite_eq_right hb]

/- WIDTH COROLLARY (2026-11-04). -/

theorem bv_term_small_rw_719_width_restricted
    (n : Nat) (s t : BitVec n)
    (h : n = 0 ∨ ∃ k : Nat, n = 2 ^ k) :
    (bvlshr s (bvshl (bvor s t) s)) = (bvlshr s (bvshl s s)) := by
  rcases h with hn0 | ⟨k, hw⟩
  · subst n; exact Subsingleton.elim _ _
  ·
    apply bv_term_small_rw_719_restricted n s t
    by_cases hz : s.toNat = 0
    · exact Or.inl hz
    by_cases hn : n ≤ s.toNat
    · exact Or.inr (Or.inl hn)
    apply Or.inr ∘ Or.inr
    have hlt : s.toNat < 2 ^ k := by omega
    have hd := Learned.Nat.not_two_pow_dvd_self_shift_of_pow_width k s.toNat (by omega) hlt
    simpa only [show 2 ^ n = 2 ^ (2 ^ k) by rw [hw]] using hd

/- 数学分析：
原自移位条件仅充分。若 s<<s=0，只需 t<<s=0 也成立；完整条件还包括 s=0。对所有 t 量化时，取 t=1 排除每个坏 s。
输入与全输入位宽的充要条件分别见 `_iff`、`_width_iff`。
进一步的位宽算术判据与待形式化部分见 ../EXACT_CONDITIONS.md。
-/

theorem bv_term_small_rw_719_iff (n : Nat) (s t : BitVec n) :
    ((bvlshr s (bvshl (bvor s t) s)) = (bvlshr s (bvshl s s))) ↔
      s.toNat = 0 ∨ ¬ 2 ^ n ∣ s.toNat * 2 ^ s.toNat ∨ 2 ^ n ∣ t.toNat * 2 ^ s.toNat := by
  by_cases hs : s = literal n 0
  · subst s; simp [bvlshr, literal]
  have hsval : s.toNat ≠ 0 := by
    intro h; apply hs; apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using h
  simp only [hsval, false_or]
  by_cases hb : bvshl s s = literal n 0
  · have hd := (bvshl_eq_zero_iff_dvd s s).mp hb
    rw [bvshl_bvor, hb, bvor_comm (literal n 0), bvor_zero, bvlshr_zero]
    simp only [hd, not_true_eq_false, false_or]
    rw [← bvshl_eq_zero_iff_dvd t s, bvlshr_bvshl_self_eq_ite]
    by_cases hc : bvshl t s = literal n 0
    · simp only [hc, ite_true]
    · simp only [hc, ite_false, eq_comm (a := literal n 0), hs]
  · have hd : ¬ 2 ^ n ∣ s.toNat * 2 ^ s.toNat := fun h => hb ((bvshl_eq_zero_iff_dvd s s).mpr h)
    exact iff_of_true (bv_term_small_rw_719_restricted n s t (Or.inr (Or.inr hd))) (Or.inl hd)

theorem bv_term_small_rw_719_width_iff (n : Nat) :
    (∀ s t : BitVec n, (bvlshr s (bvshl (bvor s t) s)) = (bvlshr s (bvshl s s))) ↔
      SelfShiftWidth n := by
  have hpoint : (∀ s t : BitVec n, (bvlshr s (bvshl (bvor s t) s)) = (bvlshr s (bvshl s s))) ↔
      ∀ s t : BitVec n, s.toNat = 0 ∨ ¬ 2 ^ n ∣ s.toNat * 2 ^ s.toNat ∨ 2 ^ n ∣ t.toNat * 2 ^ s.toNat := by
    constructor
    · intro h s t; exact (bv_term_small_rw_719_iff n s t).mp (h s t)
    · intro h s t; exact (bv_term_small_rw_719_iff n s t).mpr (h s t)
  rw [hpoint]
  rw [forall_bitvec_toNat_iff (n := n) (fun a d => a = 0 ∨ ¬ 2 ^ n ∣ a * 2 ^ a ∨ 2 ^ n ∣ d * 2 ^ a)]
  constructor
  · intro h a hpos hn hdiv
    have hap : a < 2 ^ n := Nat.lt_trans hn Nat.lt_two_pow_self
    have hp : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    have hc := h a hap 1 hp
    rcases hc with hc | hc | hc
    · omega
    · exact hc hdiv
    · simp only [Nat.one_mul] at hc
      have hlt : 2 ^ a < 2 ^ n := Nat.pow_lt_pow_right (by decide) hn
      have hz := Nat.eq_zero_of_dvd_of_lt hc hlt
      have := Nat.two_pow_pos a
      omega
  · intro h a ha d hd
    have hc := selfShiftWidth_iff.mp h a ha
    rcases hc with hc | hc | hc
    · exact Or.inl hc
    · exact Or.inr (Or.inr (Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 hc) d))
    · exact Or.inr (Or.inl hc)

end BV.QF_BV.Unsat
