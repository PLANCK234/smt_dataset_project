/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_294.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (right shifts by different counts):
The counts are a(P-1-a) mod P and -(P-1-a) mod P; the right shifts of a by them are compared. t is free.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_294 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvmul s (bvnot s))) ≠ (bvlshr s (bvneg (bvnot s)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_294_condition (n a b : Nat) : Prop :=
  RightDifferent n a ((a * (2 ^ n - 1 - a)) % 2 ^ n) ((2 ^ n - (2 ^ n - 1 - a)) % 2 ^ n)

instance (n a b : Nat) : Decidable (bv_term_small_rw_294_condition n a b) := by
  unfold bv_term_small_rw_294_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_294_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_294_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_294_solutions n p) := by
  unfold bv_term_small_rw_294_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_294_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_294 n s t ↔ bv_term_small_rw_294_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_294, bv_term_small_rw_294_condition, toNat_bvmul, toNat_bvneg, toNat_bvnot] using
    (right_different_iff s (bvmul s (bvnot s)) (bvneg (bvnot s)))

theorem bv_term_small_rw_294_solutions_iff (n a b : Nat) :
    bv_term_small_rw_294_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_294 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_294_condition n) (bv_term_small_rw_294 n)
    (bv_term_small_rw_294_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_294_sat32 :
    bv_term_small_rw_294 32 (literal 32 833855397) (literal 32 0) := by
  unfold bv_term_small_rw_294
  decide

end BV.QF_BV.Sat
