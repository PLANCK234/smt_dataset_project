/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_327.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (right shifts by different counts):
With c=L(b,a), the outer counts are ac mod P and c; count changes from multiplication wraparound pass through the right-shift threshold.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_327 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvmul s (bvshl t s))) ≠ (bvlshr s (bvshl t s))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_327_condition (n a b : Nat) : Prop :=
  RightDifferent n a ((a * (L n b a)) % 2 ^ n) (L n b a)

instance (n a b : Nat) : Decidable (bv_term_small_rw_327_condition n a b) := by
  unfold bv_term_small_rw_327_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_327_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_327_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_327_solutions n p) := by
  unfold bv_term_small_rw_327_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_327_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_327 n s t ↔ bv_term_small_rw_327_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_327, bv_term_small_rw_327_condition, toNat_bvmul, toNat_left] using
    (right_different_iff s (bvmul s (bvshl t s)) (bvshl t s))

theorem bv_term_small_rw_327_solutions_iff (n a b : Nat) :
    bv_term_small_rw_327_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_327 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_327_condition n) (bv_term_small_rw_327 n)
    (bv_term_small_rw_327_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_327_sat32 :
    bv_term_small_rw_327 32 (literal 32 2) (literal 32 536870912) := by
  unfold bv_term_small_rw_327
  decide

end BV.QF_BV.Sat
