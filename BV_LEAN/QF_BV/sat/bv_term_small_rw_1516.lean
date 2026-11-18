/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1516.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (high-bit difference under a common right shift):
The modular sums b+(a AND b) and a+b are both shifted right by a. Bits below the count are irrelevant; the high bits of their XOR determine the solutions.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1516 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr (bvadd t (bvand s t)) s) ≠ (bvlshr (bvadd s t) s)

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1516_condition (n a b : Nat) : Prop :=
  RightNonzero n (((b + (a &&& b)) % 2 ^ n) ^^^ ((a + b) % 2 ^ n)) a

instance (n a b : Nat) : Decidable (bv_term_small_rw_1516_condition n a b) := by
  unfold bv_term_small_rw_1516_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1516_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1516_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1516_solutions n p) := by
  unfold bv_term_small_rw_1516_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1516_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1516 n s t ↔ bv_term_small_rw_1516_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1516, bv_term_small_rw_1516_condition, toNat_bvadd, toNat_bvand] using
    (common_right_different_iff (bvadd t (bvand s t)) (bvadd s t) s)

theorem bv_term_small_rw_1516_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1516_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1516 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1516_condition n) (bv_term_small_rw_1516 n)
    (bv_term_small_rw_1516_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1516_sat32 :
    bv_term_small_rw_1516 32 (literal 32 3) (literal 32 5) := by
  unfold bv_term_small_rw_1516
  decide

end BV.QF_BV.Sat
