/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_710.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (right shifts by different counts):
The counts are (a+b) mod P and the complement of b, each shifted left by a; the smaller threshold decides whether the outer right shift sees the difference.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_710 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvshl (bvadd s t) s)) ≠ (bvlshr s (bvshl (bvnot t) s))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_710_condition (n a b : Nat) : Prop :=
  RightDifferent n a (L n ((a + b) % 2 ^ n) a) (L n (2 ^ n - 1 - b) a)

instance (n a b : Nat) : Decidable (bv_term_small_rw_710_condition n a b) := by
  unfold bv_term_small_rw_710_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_710_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_710_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_710_solutions n p) := by
  unfold bv_term_small_rw_710_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_710_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_710 n s t ↔ bv_term_small_rw_710_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_710, bv_term_small_rw_710_condition, toNat_bvadd, toNat_bvnot, toNat_left] using
    (right_different_iff s (bvshl (bvadd s t) s) (bvshl (bvnot t) s))

theorem bv_term_small_rw_710_solutions_iff (n a b : Nat) :
    bv_term_small_rw_710_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_710 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_710_condition n) (bv_term_small_rw_710 n)
    (bv_term_small_rw_710_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_710_sat32 :
    bv_term_small_rw_710 32 (literal 32 2) (literal 32 4294967295) := by
  unfold bv_term_small_rw_710
  decide

end BV.QF_BV.Sat
