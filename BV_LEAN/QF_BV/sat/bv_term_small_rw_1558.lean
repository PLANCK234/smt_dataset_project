/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1558.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (overlapping counts of sequential left shifts):
With X=R(a,b), solutions are exactly a AND b ≠ 0 with X shifted left by a OR b nonzero; X=0 is excluded automatically.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1558 (n : Nat) (s t : BitVec n) : Prop :=
  (bvshl (bvshl (bvlshr s t) s) t) ≠ (bvshl (bvlshr s t) (bvor s t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1558_condition (n a b : Nat) : Prop :=
  SequentialLeftDifferent n (R n a b) a b

instance (n a b : Nat) : Decidable (bv_term_small_rw_1558_condition n a b) := by
  unfold bv_term_small_rw_1558_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1558_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1558_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1558_solutions n p) := by
  unfold bv_term_small_rw_1558_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1558_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1558 n s t ↔ bv_term_small_rw_1558_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1558, bv_term_small_rw_1558_condition, toNat_right] using
    (sequential_left_different_iff (bvlshr s t) s t)

theorem bv_term_small_rw_1558_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1558_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1558 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1558_condition n) (bv_term_small_rw_1558 n)
    (bv_term_small_rw_1558_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1558_sat32 :
    bv_term_small_rw_1558 32 (literal 32 3) (literal 32 1) := by
  unfold bv_term_small_rw_1558
  decide

end BV.QF_BV.Sat
