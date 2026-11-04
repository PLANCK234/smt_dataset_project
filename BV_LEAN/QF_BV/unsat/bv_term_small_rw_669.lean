/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_669.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.ExactConditions
import LEMMAS_learned.BitVec.Shift.Conditions
import LEMMAS_learned.BitVec.Shift.Quotient
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (toNat)

def bv_term_small_rw_669 : Prop :=
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvshl (bvnot (literal n 0)) s)) = (bvlshr s (bvshl s s))

theorem bv_term_small_rw_669_counterexample : ¬ bv_term_small_rw_669 := by
  intro h
  have hbad : ¬ ((bvlshr (literal 3 2) (bvshl (bvnot (literal 3 0)) (literal 3 2))) = (bvlshr (literal 3 2) (bvshl (literal 3 2) (literal 3 2)))) := by decide
  exact hbad (h 3 (literal 3 2) (literal 3 0))

theorem bv_term_small_rw_669_restricted
    (n : Nat) (s t : BitVec n)
    (h : s.toNat = 0 ∨ n ≤ s.toNat ∨ ¬ 2 ^ n ∣ s.toNat * 2 ^ s.toNat) :
    (bvlshr s (bvshl (bvnot (literal n 0)) s)) = (bvlshr s (bvshl s s)) := by
  rcases h with hz | hn | hd
  · have hs : s = literal n 0 := by
      apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using hz
    subst s; simp [bvshl_eq_shiftLeft, bvlshr, literal]
  · rw [bvshl_large _ _ hn, bvshl_large _ _ hn]
  · have hb : bvshl s s ≠ literal n 0 := fun hb => hd ((bvshl_eq_zero_iff_dvd s s).mp hb)
    have hs : s.toNat < n := by
      by_cases hn : n ≤ s.toNat
      · exact False.elim (hb (bvshl_large s s hn))
      · omega
    have hl := width_le_toNat_bvshl_bvnot_zero s hs
    rw [bvlshr_large _ _ hl, bvlshr_bvshl_self_eq_ite, ite_eq_right hb]

/- WIDTH COROLLARY (2026-11-04). -/

theorem bv_term_small_rw_669_width_restricted
    (n : Nat) (s t : BitVec n)
    (h : n = 0 ∨ ∃ k : Nat, n = 2 ^ k) :
    (bvlshr s (bvshl (bvnot (literal n 0)) s)) = (bvlshr s (bvshl s s)) := by
  rcases h with hn0 | ⟨k, hw⟩
  · subst n; exact Subsingleton.elim _ _
  ·
    apply bv_term_small_rw_669_restricted n s t
    by_cases hz : s.toNat = 0
    · exact Or.inl hz
    by_cases hn : n ≤ s.toNat
    · exact Or.inr (Or.inl hn)
    apply Or.inr ∘ Or.inr
    have hlt : s.toNat < 2 ^ k := by omega
    have hd := Learned.Nat.not_two_pow_dvd_self_shift_of_pow_width k s.toNat (by omega) hlt
    simpa only [show 2 ^ n = 2 ^ (2 ^ k) by rw [hw]] using hd

/- 数学分析：
s=0 或 s>=n 时成立；0<s<n 时，全一内层清空左侧，右侧恰在自移位非零时也为零，得到整除条件的必要性。
输入与全输入位宽的充要条件分别见 `_iff`、`_width_iff`。
进一步的位宽算术判据与待形式化部分见 ../EXACT_CONDITIONS.md。
-/

theorem bv_term_small_rw_669_iff (n : Nat) (s t : BitVec n) :
    ((bvlshr s (bvshl (bvnot (literal n 0)) s)) = (bvlshr s (bvshl s s))) ↔
      SelfShiftAdmissible n s.toNat := by
  constructor
  · intro he
    by_cases hz : s.toNat = 0
    · exact Or.inl hz
    by_cases hn : n ≤ s.toNat
    · exact Or.inr (Or.inl hn)
    apply Or.inr ∘ Or.inr
    intro hd
    have hb := (bvshl_eq_zero_iff_dvd s s).mpr hd
    have hl := width_le_toNat_bvshl_bvnot_zero s (by omega)
    rw [bvlshr_large _ _ hl, hb, bvlshr_zero] at he
    have hs := congrArg toNat he
    simp only [toNat_literal, Nat.zero_mod] at hs
    omega
  · exact bv_term_small_rw_669_restricted n s t

theorem bv_term_small_rw_669_width_iff (n : Nat) :
    (∀ s t : BitVec n, (bvlshr s (bvshl (bvnot (literal n 0)) s)) = (bvlshr s (bvshl s s))) ↔
      SelfShiftWidth n := by
  have hpoint : (∀ s t : BitVec n, (bvlshr s (bvshl (bvnot (literal n 0)) s)) = (bvlshr s (bvshl s s))) ↔
      ∀ s t : BitVec n, SelfShiftAdmissible n s.toNat := by
    constructor
    · intro h s t; exact (bv_term_small_rw_669_iff n s t).mp (h s t)
    · intro h s t; exact (bv_term_small_rw_669_iff n s t).mpr (h s t)
  rw [hpoint]
  rw [forall_bitvec_toNat_iff (n := n) (fun a d => SelfShiftAdmissible n a), selfShiftWidth_iff]
  constructor
  · intro h a ha; exact h a ha 0 (Nat.two_pow_pos n)
  · intro h a ha d hd; exact h a ha

end BV.QF_BV.Unsat
