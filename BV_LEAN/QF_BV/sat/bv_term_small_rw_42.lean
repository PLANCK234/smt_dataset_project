/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_42.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (right shifts by different counts):
The counts are L(a,b) and R(a,b). Different counts are not enough: a must reach the power-of-two threshold of the smaller one.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_42 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvshl s t)) ≠ (bvlshr s (bvlshr s t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_42_condition (n a b : Nat) : Prop :=
  RightDifferent n a (L n a b) (R n a b)

instance (n a b : Nat) : Decidable (bv_term_small_rw_42_condition n a b) := by
  unfold bv_term_small_rw_42_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_42_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_42_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_42_solutions n p) := by
  unfold bv_term_small_rw_42_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_42_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_42 n s t ↔ bv_term_small_rw_42_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_42, bv_term_small_rw_42_condition, toNat_right, toNat_left] using
    (right_different_iff s (bvshl s t) (bvlshr s t))

theorem bv_term_small_rw_42_solutions_iff (n a b : Nat) :
    bv_term_small_rw_42_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_42 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_42_condition n) (bv_term_small_rw_42 n)
    (bv_term_small_rw_42_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_42_sat32 :
    bv_term_small_rw_42 32 (literal 32 1) (literal 32 1) := by
  unfold bv_term_small_rw_42
  decide

end BV.QF_BV.Sat
