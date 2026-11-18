/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_36.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (nonzero right-shift threshold):
Let q=(a+b) mod P; the expression is nonzero iff a reaches 2^q. Large a, b can wrap to a small q.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_36 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvadd s t)) ≠ (literal n 0)

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_36_condition (n a b : Nat) : Prop :=
  RightNonzero n a ((a + b) % 2 ^ n)

instance (n a b : Nat) : Decidable (bv_term_small_rw_36_condition n a b) := by
  unfold bv_term_small_rw_36_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_36_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_36_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_36_solutions n p) := by
  unfold bv_term_small_rw_36_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_36_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_36 n s t ↔ bv_term_small_rw_36_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_36, bv_term_small_rw_36_condition, toNat_bvadd] using
    (right_nonzero_iff s (bvadd s t))

theorem bv_term_small_rw_36_solutions_iff (n a b : Nat) :
    bv_term_small_rw_36_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_36 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_36_condition n) (bv_term_small_rw_36 n)
    (bv_term_small_rw_36_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_36_sat32 :
    bv_term_small_rw_36 32 (literal 32 1) (literal 32 4294967295) := by
  unfold bv_term_small_rw_36
  decide

end BV.QF_BV.Sat
