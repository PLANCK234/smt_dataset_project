/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_460.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (left/right shift divisibility):
q=b AND R(b,a); balanced patterns of the outer left/right shifts are excluded.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_460 (n : Nat) (s t : BitVec n) : Prop :=
  (bvshl s (bvand t (bvlshr t s))) ≠ (bvlshr s (bvand t (bvlshr t s)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_460_condition (n a b : Nat) : Prop :=
  ShiftDifferent n a (b &&& (R n b a))

instance (n a b : Nat) : Decidable (bv_term_small_rw_460_condition n a b) := by
  unfold bv_term_small_rw_460_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_460_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_460_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_460_solutions n p) := by
  unfold bv_term_small_rw_460_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_460_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_460 n s t ↔ bv_term_small_rw_460_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_460, bv_term_small_rw_460_condition, toNat_bvand, toNat_right] using
    (shift_different_iff s (bvand t (bvlshr t s)))

theorem bv_term_small_rw_460_solutions_iff (n a b : Nat) :
    bv_term_small_rw_460_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_460 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_460_condition n) (bv_term_small_rw_460 n)
    (bv_term_small_rw_460_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_460_sat32 :
    bv_term_small_rw_460 32 (literal 32 1) (literal 32 3) := by
  unfold bv_term_small_rw_460
  decide

end BV.QF_BV.Sat
