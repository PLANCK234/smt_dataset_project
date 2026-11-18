/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_45.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (right shifts by different counts):
The counts are t shifted left and right by s. Both outer operations shift a right, so the counts and the smaller threshold determine the solutions.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_45 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvshl t s)) ≠ (bvlshr s (bvlshr t s))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_45_condition (n a b : Nat) : Prop :=
  RightDifferent n a (L n b a) (R n b a)

instance (n a b : Nat) : Decidable (bv_term_small_rw_45_condition n a b) := by
  unfold bv_term_small_rw_45_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_45_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_45_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_45_solutions n p) := by
  unfold bv_term_small_rw_45_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_45_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_45 n s t ↔ bv_term_small_rw_45_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_45, bv_term_small_rw_45_condition, toNat_right, toNat_left] using
    (right_different_iff s (bvshl t s) (bvlshr t s))

theorem bv_term_small_rw_45_solutions_iff (n a b : Nat) :
    bv_term_small_rw_45_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_45 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_45_condition n) (bv_term_small_rw_45 n)
    (bv_term_small_rw_45_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_45_sat32 :
    bv_term_small_rw_45 32 (literal 32 1) (literal 32 1) := by
  unfold bv_term_small_rw_45
  decide

end BV.QF_BV.Sat
