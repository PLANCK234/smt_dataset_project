/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_25.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (left/right shift divisibility):
The count is q=P-1-b, the complement of t. 0<q<n is only necessary; balanced patterns where the left and right shifts agree are excluded.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_25 (n : Nat) (s t : BitVec n) : Prop :=
  (bvshl s (bvnot t)) ≠ (bvlshr s (bvnot t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_25_condition (n a b : Nat) : Prop :=
  ShiftDifferent n a (2 ^ n - 1 - b)

instance (n a b : Nat) : Decidable (bv_term_small_rw_25_condition n a b) := by
  unfold bv_term_small_rw_25_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_25_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_25_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_25_solutions n p) := by
  unfold bv_term_small_rw_25_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_25_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_25 n s t ↔ bv_term_small_rw_25_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_25, bv_term_small_rw_25_condition, toNat_bvnot] using
    (shift_different_iff s (bvnot t))

theorem bv_term_small_rw_25_solutions_iff (n a b : Nat) :
    bv_term_small_rw_25_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_25 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_25_condition n) (bv_term_small_rw_25 n)
    (bv_term_small_rw_25_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_25_sat32 :
    bv_term_small_rw_25 32 (literal 32 1) (literal 32 4294967294) := by
  unfold bv_term_small_rw_25
  decide

end BV.QF_BV.Sat
