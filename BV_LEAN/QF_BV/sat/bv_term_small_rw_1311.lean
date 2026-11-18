/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1311.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (nonzero right-shift threshold):
U=ab mod P is shifted right by a OR b; the result is nonzero iff the count is below n and U reaches its power-of-two threshold.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1311 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr (bvmul s t) (bvor s t)) ≠ (literal n 0)

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1311_condition (n a b : Nat) : Prop :=
  RightNonzero n ((a * b) % 2 ^ n) (a ||| b)

instance (n a b : Nat) : Decidable (bv_term_small_rw_1311_condition n a b) := by
  unfold bv_term_small_rw_1311_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1311_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1311_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1311_solutions n p) := by
  unfold bv_term_small_rw_1311_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1311_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1311 n s t ↔ bv_term_small_rw_1311_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1311, bv_term_small_rw_1311_condition, toNat_bvmul, toNat_bvor] using
    (right_nonzero_iff (bvmul s t) (bvor s t))

theorem bv_term_small_rw_1311_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1311_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1311 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1311_condition n) (bv_term_small_rw_1311 n)
    (bv_term_small_rw_1311_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1311_sat32 :
    bv_term_small_rw_1311 32 (literal 32 2) (literal 32 2) := by
  unfold bv_term_small_rw_1311
  decide

end BV.QF_BV.Sat
