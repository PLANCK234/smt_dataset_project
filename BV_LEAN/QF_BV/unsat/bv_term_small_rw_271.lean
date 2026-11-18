/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_271.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.ExactConditions
import LEMMAS_learned.BitVec.Shift.Conditions
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

def bv_term_small_rw_271 : Prop :=
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvnot (bvshl t t))) = (literal n 0)

theorem bv_term_small_rw_271_counterexample : ¬ bv_term_small_rw_271 := by
  intro h
  have hbad : ¬ ((bvshl (literal 2 1) (bvnot (bvshl (literal 2 1) (literal 2 1)))) = (literal 2 0)) := by decide
  exact hbad (h 2 (literal 2 1) (literal 2 1))

theorem bv_term_small_rw_271_restricted
    (n : Nat) (s t : BitVec n)
    (h : n ≠ 2) :
    (bvshl s (bvnot (bvshl t t))) = (literal n 0) := by
  exact bvshl_large s _ (width_le_toNat_bvnot_bvshl_self t h)

/- Analysis:
For n=2 and t=1 the outer shift is left by 1, which is zero iff s is even; otherwise it is always zero.
Exact conditions: `_iff` per input, `_width_iff` per width; see ../EXACT_CONDITIONS.md.
-/

theorem bv_term_small_rw_271_iff (n : Nat) (s t : BitVec n) :
    ((bvshl s (bvnot (bvshl t t))) = (literal n 0)) ↔
      n ≠ 2 ∨ t.toNat ≠ 1 ∨ s.toNat % 2 = 0 := by
  by_cases hn : n = 2
  · subst n
    have hs := s.isLt
    have ht := t.isLt
    have hsc : s.toNat = 0 ∨ s.toNat = 1 ∨ s.toNat = 2 ∨ s.toNat = 3 := by omega
    have htc : t.toNat = 0 ∨ t.toNat = 1 ∨ t.toNat = 2 ∨ t.toNat = 3 := by omega
    rcases hsc with hs0 | hs1 | hs2 | hs3 <;>
      rcases htc with ht0 | ht1 | ht2 | ht3 <;>
      simp_all [eq_iff_toNat_eq, toNat_bvshl]
  exact iff_of_true (bv_term_small_rw_271_restricted n s t hn) (Or.inl hn)

theorem bv_term_small_rw_271_width_iff (n : Nat) :
    (∀ s t : BitVec n, (bvshl s (bvnot (bvshl t t))) = (literal n 0)) ↔
      n ≠ 2 := by
  constructor
  · intro h hn
    subst n
    have hc := (bv_term_small_rw_271_iff 2 (literal 2 1) (literal 2 1)).mp (h (literal 2 1) (literal 2 1))
    simp at hc
  · intro hn s t
    exact bv_term_small_rw_271_restricted n s t hn

end BV.QF_BV.Unsat
