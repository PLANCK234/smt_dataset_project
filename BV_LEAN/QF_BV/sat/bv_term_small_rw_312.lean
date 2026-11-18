/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_312.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (difference under a common mask):
Both sides share the mask a; SAT iff the XOR of the left and right shifts meets a.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_312 (n : Nat) (s t : BitVec n) : Prop :=
  (bvand s (bvshl s (bvadd s t))) ≠ (bvand s (bvlshr s (bvadd s t)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_312_condition (n a b : Nat) : Prop :=
  a &&& ((L n a ((a + b) % 2 ^ n)) ^^^ (R n a ((a + b) % 2 ^ n))) ≠ 0

instance (n a b : Nat) : Decidable (bv_term_small_rw_312_condition n a b) := by
  unfold bv_term_small_rw_312_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_312_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_312_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_312_solutions n p) := by
  unfold bv_term_small_rw_312_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_312_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_312 n s t ↔ bv_term_small_rw_312_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_312, bv_term_small_rw_312_condition, toNat_bvadd, toNat_right, toNat_left] using
    (masked_different_iff s (bvshl s (bvadd s t)) (bvlshr s (bvadd s t)))

theorem bv_term_small_rw_312_solutions_iff (n a b : Nat) :
    bv_term_small_rw_312_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_312 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_312_condition n) (bv_term_small_rw_312 n)
    (bv_term_small_rw_312_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_312_sat32 :
    bv_term_small_rw_312 32 (literal 32 3) (literal 32 4294967294) := by
  unfold bv_term_small_rw_312
  decide

end BV.QF_BV.Sat
