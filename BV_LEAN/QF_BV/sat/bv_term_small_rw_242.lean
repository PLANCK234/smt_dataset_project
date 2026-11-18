/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_242.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (left/right shift divisibility):
The count is the finite complement P-1-(ab mod P), not an unbounded bitwise NOT; the outer comparison uses the left/right shift criterion.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_242 (n : Nat) (s t : BitVec n) : Prop :=
  (bvshl s (bvnot (bvmul s t))) ≠ (bvlshr s (bvnot (bvmul s t)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_242_condition (n a b : Nat) : Prop :=
  ShiftDifferent n a (2 ^ n - 1 - ((a * b) % 2 ^ n))

instance (n a b : Nat) : Decidable (bv_term_small_rw_242_condition n a b) := by
  unfold bv_term_small_rw_242_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_242_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_242_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_242_solutions n p) := by
  unfold bv_term_small_rw_242_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_242_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_242 n s t ↔ bv_term_small_rw_242_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_242, bv_term_small_rw_242_condition, toNat_bvmul, toNat_bvnot] using
    (shift_different_iff s (bvnot (bvmul s t)))

theorem bv_term_small_rw_242_solutions_iff (n a b : Nat) :
    bv_term_small_rw_242_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_242 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_242_condition n) (bv_term_small_rw_242 n)
    (bv_term_small_rw_242_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_242_sat32 :
    bv_term_small_rw_242 32 (literal 32 1) (literal 32 4294967294) := by
  unfold bv_term_small_rw_242
  decide

end BV.QF_BV.Sat
