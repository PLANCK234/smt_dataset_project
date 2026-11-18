/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_424.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (left/right shift divisibility):
q is b shifted right by ab mod P; the non-divisibility condition for the outer left/right shifts characterizes all a, b.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_424 (n : Nat) (s t : BitVec n) : Prop :=
  (bvshl s (bvlshr t (bvmul s t))) ≠ (bvlshr s (bvlshr t (bvmul s t)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_424_condition (n a b : Nat) : Prop :=
  ShiftDifferent n a (R n b ((a * b) % 2 ^ n))

instance (n a b : Nat) : Decidable (bv_term_small_rw_424_condition n a b) := by
  unfold bv_term_small_rw_424_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_424_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_424_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_424_solutions n p) := by
  unfold bv_term_small_rw_424_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_424_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_424 n s t ↔ bv_term_small_rw_424_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_424, bv_term_small_rw_424_condition, toNat_right, toNat_bvmul] using
    (shift_different_iff s (bvlshr t (bvmul s t)))

theorem bv_term_small_rw_424_solutions_iff (n a b : Nat) :
    bv_term_small_rw_424_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_424 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_424_condition n) (bv_term_small_rw_424 n)
    (bv_term_small_rw_424_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_424_sat32 :
    bv_term_small_rw_424 32 (literal 32 14) (literal 32 2147483650) := by
  unfold bv_term_small_rw_424
  decide

end BV.QF_BV.Sat
