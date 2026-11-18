/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1391.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (overlapping counts of sequential left shifts):
SAT iff b AND L(a,a) ≠ 0 and a shifted left by b OR L(a,a) is nonzero; the second condition excludes all clearing cases.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1391 (n : Nat) (s t : BitVec n) : Prop :=
  (bvshl (bvshl s t) (bvshl s s)) ≠ (bvshl s (bvor t (bvshl s s)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1391_condition (n a b : Nat) : Prop :=
  SequentialLeftDifferent n a b (L n a a)

instance (n a b : Nat) : Decidable (bv_term_small_rw_1391_condition n a b) := by
  unfold bv_term_small_rw_1391_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1391_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1391_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1391_solutions n p) := by
  unfold bv_term_small_rw_1391_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1391_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1391 n s t ↔ bv_term_small_rw_1391_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1391, bv_term_small_rw_1391_condition, toNat_left] using
    (sequential_left_different_iff s t (bvshl s s))

theorem bv_term_small_rw_1391_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1391_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1391 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1391_condition n) (bv_term_small_rw_1391 n)
    (bv_term_small_rw_1391_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1391_sat32 :
    bv_term_small_rw_1391 32 (literal 32 1) (literal 32 2) := by
  unfold bv_term_small_rw_1391
  decide

end BV.QF_BV.Sat
