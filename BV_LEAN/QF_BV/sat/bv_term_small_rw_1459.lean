/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1459.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (high-bit difference under a common right shift):
(a+(a AND b)) mod P and (a+b) mod P are both shifted right by b; a difference must survive in the high bits.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1459 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr (bvadd s (bvand s t)) t) ≠ (bvlshr (bvadd s t) t)

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1459_condition (n a b : Nat) : Prop :=
  RightNonzero n (((a + (a &&& b)) % 2 ^ n) ^^^ ((a + b) % 2 ^ n)) b

instance (n a b : Nat) : Decidable (bv_term_small_rw_1459_condition n a b) := by
  unfold bv_term_small_rw_1459_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1459_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1459_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1459_solutions n p) := by
  unfold bv_term_small_rw_1459_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1459_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1459 n s t ↔ bv_term_small_rw_1459_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1459, bv_term_small_rw_1459_condition, toNat_bvadd, toNat_bvand] using
    (common_right_different_iff (bvadd s (bvand s t)) (bvadd s t) t)

theorem bv_term_small_rw_1459_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1459_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1459 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1459_condition n) (bv_term_small_rw_1459 n)
    (bv_term_small_rw_1459_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1459_sat32 :
    bv_term_small_rw_1459 32 (literal 32 5) (literal 32 3) := by
  unfold bv_term_small_rw_1459
  decide

end BV.QF_BV.Sat
