/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_158.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (overlapping counts of sequential left shifts):
Sequential left shifts add their counts, and the sum is OR + AND. Solutions are exactly AND ≠ 0 with a nonzero shift by the OR count; a positive left shift has no nonzero fixed point.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_158 (n : Nat) (s t : BitVec n) : Prop :=
  (bvshl (bvshl s s) t) ≠ (bvshl s (bvor s t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_158_condition (n a b : Nat) : Prop :=
  SequentialLeftDifferent n a a b

instance (n a b : Nat) : Decidable (bv_term_small_rw_158_condition n a b) := by
  unfold bv_term_small_rw_158_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_158_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_158_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_158_solutions n p) := by
  unfold bv_term_small_rw_158_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_158_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_158 n s t ↔ bv_term_small_rw_158_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_158, bv_term_small_rw_158_condition] using
    (sequential_left_different_iff s s t)

theorem bv_term_small_rw_158_solutions_iff (n a b : Nat) :
    bv_term_small_rw_158_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_158 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_158_condition n) (bv_term_small_rw_158 n)
    (bv_term_small_rw_158_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_158_sat32 :
    bv_term_small_rw_158 32 (literal 32 1) (literal 32 1) := by
  unfold bv_term_small_rw_158
  decide

end BV.QF_BV.Sat
