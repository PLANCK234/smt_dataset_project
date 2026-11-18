/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_707.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (common set bits):
The self left shift of a is shifted right by b and intersected with a; the truncation order matters.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_707 (n : Nat) (s t : BitVec n) : Prop :=
  (bvand s (bvlshr (bvshl s s) t)) ≠ (literal n 0)

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_707_condition (n a b : Nat) : Prop :=
  a &&& (R n (L n a a) b) ≠ 0

instance (n a b : Nat) : Decidable (bv_term_small_rw_707_condition n a b) := by
  unfold bv_term_small_rw_707_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_707_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_707_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_707_solutions n p) := by
  unfold bv_term_small_rw_707_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_707_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_707 n s t ↔ bv_term_small_rw_707_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_707, bv_term_small_rw_707_condition, toNat_right, toNat_left] using
    (and_nonzero_iff s (bvlshr (bvshl s s) t))

theorem bv_term_small_rw_707_solutions_iff (n a b : Nat) :
    bv_term_small_rw_707_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_707 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_707_condition n) (bv_term_small_rw_707 n)
    (bv_term_small_rw_707_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_707_sat32 :
    bv_term_small_rw_707 32 (literal 32 1) (literal 32 1) := by
  unfold bv_term_small_rw_707
  decide

end BV.QF_BV.Sat
