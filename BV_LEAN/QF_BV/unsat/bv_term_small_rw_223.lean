/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_223.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.ExactConditions
import Init.Data.Nat.MinMax
import LEMMAS_learned.Nat.Pow
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec

def bv_term_small_rw_223 : Prop :=
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvnot (bvneg s))) = (bvlshr (bvadd s s) s)

theorem bv_term_small_rw_223_counterexample : ¬ bv_term_small_rw_223 := by
  intro h
  have hbad : ¬ ((bvlshr (literal 1 1) (bvnot (bvneg (literal 1 1)))) = (bvlshr (bvadd (literal 1 1) (literal 1 1)) (literal 1 1))) := by decide
  exact hbad (h 1 (literal 1 1) (literal 1 0))

theorem bv_term_small_rw_223_restricted
    (n : Nat) (s t : BitVec n)
    (h : n = 0 ∨ 3 ≤ n) :
    (bvlshr s (bvnot (bvneg s))) = (bvlshr (bvadd s s) s) := by
  rcases h with hn0 | hn
  · subst n; exact Subsingleton.elim _ _
  ·
    have hp : 8 ≤ 2 ^ n := (Nat.pow_le_pow_right (n := 2) (by decide) hn)
    have hs := s.isLt
    apply toNat_injective
    simp only [toNat_bvlshr, toNat_bvnot, toNat_bvneg, toNat_bvadd]
    by_cases hz : s.toNat = 0
    · simp only [hz, Nat.sub_zero, Nat.mod_self, Nat.zero_div, Nat.zero_add, Nat.zero_mod]
    have hneg : (2 ^ n - s.toNat) % 2 ^ n = 2 ^ n - s.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hneg, show 2 ^ n - 1 - (2 ^ n - s.toNat) = s.toNat - 1 by omega]
    by_cases h1 : s.toNat = 1
    · rw [h1]; simp only [Nat.reduceSub, Nat.pow_zero, Nat.div_one, Nat.reduceAdd, Nat.pow_one,
        Nat.mod_eq_of_lt (show 2 < 2 ^ n by omega)]
    by_cases h2 : s.toNat = 2
    · rw [h2]; simp only [Nat.reduceSub, Nat.pow_one, Nat.reduceAdd, Nat.reducePow,
        Nat.mod_eq_of_lt (show 4 < 2 ^ n by omega)]
    have hbound := Learned.Nat.two_mul_lt_two_pow_of_three_le s.toNat (by omega)
    have he : 2 ^ s.toNat = 2 ^ (s.toNat - 1) * 2 := by
      conv => lhs; rw [show s.toNat = s.toNat - 1 + 1 by omega, Nat.pow_succ]
    rw [Nat.div_eq_of_lt (show s.toNat < 2 ^ (s.toNat - 1) by omega),
      Nat.div_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (show s.toNat + s.toNat < 2 ^ s.toNat by omega))]

theorem bv_term_small_rw_223_counterexample_width2 :
    bvlshr (literal 2 2) (bvnot (bvneg (literal 2 2))) ≠
      bvlshr (bvadd (literal 2 2) (literal 2 2)) (literal 2 2) := by decide

/- 数学分析：
当 a>0 时补码负值为 a-1；a>=3 时两商为零。唯一坏输入是 (n,a)=(1,1)、(2,2)。对全部输入量化后，坏位宽恰为 1、2。
输入与全输入位宽的充要条件分别见 `_iff`、`_width_iff`。
进一步的位宽算术判据与待形式化部分见 ../EXACT_CONDITIONS.md。
-/

theorem bv_term_small_rw_223_iff (n : Nat) (s t : BitVec n) :
    ((bvlshr s (bvnot (bvneg s))) = (bvlshr (bvadd s s) s)) ↔
      (n ≠ 1 ∨ s.toNat ≠ 1) ∧ (n ≠ 2 ∨ s.toNat ≠ 2) := by
  by_cases h1 : n = 1
  · subst n
    have hs := s.isLt
    have ht := t.isLt
    have hsc : s.toNat = 0 ∨ s.toNat = 1 := by omega
    have htc : t.toNat = 0 ∨ t.toNat = 1 := by omega
    rcases hsc with hs0 | hs1 <;>
      rcases htc with ht0 | ht1 <;>
      simp_all [eq_iff_toNat_eq]
  by_cases h2 : n = 2
  · subst n
    have hs := s.isLt
    have ht := t.isLt
    have hsc : s.toNat = 0 ∨ s.toNat = 1 ∨ s.toNat = 2 ∨ s.toNat = 3 := by omega
    have htc : t.toNat = 0 ∨ t.toNat = 1 ∨ t.toNat = 2 ∨ t.toNat = 3 := by omega
    rcases hsc with hs0 | hs1 | hs2 | hs3 <;>
      rcases htc with ht0 | ht1 | ht2 | ht3 <;>
      simp_all [eq_iff_toNat_eq]
  exact iff_of_true (bv_term_small_rw_223_restricted n s t (by omega)) ⟨Or.inl h1, Or.inl h2⟩

theorem bv_term_small_rw_223_width_iff (n : Nat) :
    (∀ s t : BitVec n, (bvlshr s (bvnot (bvneg s))) = (bvlshr (bvadd s s) s)) ↔
      n = 0 ∨ 3 ≤ n := by
  constructor
  · intro h
    by_cases h1 : n = 1
    · subst n
      have hc := (bv_term_small_rw_223_iff 1 (literal 1 1) (literal 1 0)).mp (h (literal 1 1) (literal 1 0))
      simp at hc
    by_cases h2 : n = 2
    · subst n
      have hc := (bv_term_small_rw_223_iff 2 (literal 2 2) (literal 2 0)).mp (h (literal 2 2) (literal 2 0))
      simp at hc
    omega
  · intro hn s t
    exact bv_term_small_rw_223_restricted n s t hn

end BV.QF_BV.Unsat
