/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_318.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (bits missing from a mask):
A left shift by a gives the right-shift count. SAT iff the quotient has bits outside the mask a.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_318 (n : Nat) (s t : BitVec n) : Prop :=
  (bvand s (bvlshr s (bvshl s t))) ≠ (bvlshr s (bvshl s t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_318_condition (n a b : Nat) : Prop :=
  (2 ^ n - 1 - a) &&& (R n a (L n a b)) ≠ 0

instance (n a b : Nat) : Decidable (bv_term_small_rw_318_condition n a b) := by
  unfold bv_term_small_rw_318_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_318_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_318_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_318_solutions n p) := by
  unfold bv_term_small_rw_318_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_318_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_318 n s t ↔ bv_term_small_rw_318_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_318, bv_term_small_rw_318_condition, toNat_right, toNat_left] using
    (mask_loss_iff s (bvlshr s (bvshl s t)))

theorem bv_term_small_rw_318_solutions_iff (n a b : Nat) :
    bv_term_small_rw_318_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_318 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_318_condition n) (bv_term_small_rw_318 n)
    (bv_term_small_rw_318_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_318_sat32 :
    bv_term_small_rw_318 32 (literal 32 268435457) (literal 32 4) := by
  unfold bv_term_small_rw_318
  decide

end BV.QF_BV.Sat
