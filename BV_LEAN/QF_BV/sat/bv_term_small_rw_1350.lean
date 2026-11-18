/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1350.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (natural sum of sequential right-shift counts):
The sequential right shifts have the natural count b+(P-1-a), without wraparound; the other count is an OR. Apply the right-shift difference criterion to the natural counts.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1350 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr (bvlshr s t) (bvnot s)) ≠ (bvlshr s (bvor t (bvnot s)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1350_condition (n a b : Nat) : Prop :=
  RightDifferent n a (b + (2 ^ n - 1 - a)) (b ||| (2 ^ n - 1 - a))

instance (n a b : Nat) : Decidable (bv_term_small_rw_1350_condition n a b) := by
  unfold bv_term_small_rw_1350_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1350_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1350_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1350_solutions n p) := by
  unfold bv_term_small_rw_1350_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1350_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1350 n s t ↔ bv_term_small_rw_1350_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1350, bv_term_small_rw_1350_condition, toNat_bvnot, toNat_bvor] using
    (nested_right_different_iff s t (bvnot s) (bvor t (bvnot s)))

theorem bv_term_small_rw_1350_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1350_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1350 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1350_condition n) (bv_term_small_rw_1350 n)
    (bv_term_small_rw_1350_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1350_sat32 :
    bv_term_small_rw_1350 32 (literal 32 4294967294) (literal 32 1) := by
  unfold bv_term_small_rw_1350
  decide

end BV.QF_BV.Sat
