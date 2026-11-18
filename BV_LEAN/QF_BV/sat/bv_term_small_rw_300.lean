/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_300.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (left/right shift divisibility):
2a mod P is the inner right-shift count and the quotient is the outer count; nested counts do not simply add. t is free.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_300 (n : Nat) (s t : BitVec n) : Prop :=
  (bvshl s (bvlshr s (bvadd s s))) ≠ (bvlshr s (bvlshr s (bvadd s s)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_300_condition (n a b : Nat) : Prop :=
  ShiftDifferent n a (R n a ((a + a) % 2 ^ n))

instance (n a b : Nat) : Decidable (bv_term_small_rw_300_condition n a b) := by
  unfold bv_term_small_rw_300_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_300_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_300_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_300_solutions n p) := by
  unfold bv_term_small_rw_300_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_300_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_300 n s t ↔ bv_term_small_rw_300_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_300, bv_term_small_rw_300_condition, toNat_bvadd, toNat_right] using
    (shift_different_iff s (bvlshr s (bvadd s s)))

theorem bv_term_small_rw_300_solutions_iff (n a b : Nat) :
    bv_term_small_rw_300_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_300 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_300_condition n) (bv_term_small_rw_300 n)
    (bv_term_small_rw_300_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_300_sat32 :
    bv_term_small_rw_300 32 (literal 32 2147483663) (literal 32 0) := by
  unfold bv_term_small_rw_300
  decide

end BV.QF_BV.Sat
