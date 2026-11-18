/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1406.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (high-bit difference under a common right shift):
b^2 mod P and ab mod P are shifted right by the same count a OR b; only XOR bits at or above the count distinguish them.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1406 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr (bvmul t t) (bvor s t)) ≠ (bvlshr (bvmul s t) (bvor s t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1406_condition (n a b : Nat) : Prop :=
  RightNonzero n (((b * b) % 2 ^ n) ^^^ ((a * b) % 2 ^ n)) (a ||| b)

instance (n a b : Nat) : Decidable (bv_term_small_rw_1406_condition n a b) := by
  unfold bv_term_small_rw_1406_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1406_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1406_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1406_solutions n p) := by
  unfold bv_term_small_rw_1406_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1406_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1406 n s t ↔ bv_term_small_rw_1406_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1406, bv_term_small_rw_1406_condition, toNat_bvmul, toNat_bvor] using
    (common_right_different_iff (bvmul t t) (bvmul s t) (bvor s t))

theorem bv_term_small_rw_1406_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1406_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1406 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1406_condition n) (bv_term_small_rw_1406 n)
    (bv_term_small_rw_1406_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1406_sat32 :
    bv_term_small_rw_1406 32 (literal 32 0) (literal 32 2) := by
  unfold bv_term_small_rw_1406
  decide

end BV.QF_BV.Sat
