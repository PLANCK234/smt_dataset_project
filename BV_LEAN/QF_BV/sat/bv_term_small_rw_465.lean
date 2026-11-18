/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_465.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (right shifts by different counts):
With c=L(b,a), the counts are bc mod P and ac mod P; c may be zero or non-invertible, so it is not cancelled.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_465 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvmul t (bvshl t s))) ≠ (bvlshr s (bvmul s (bvshl t s)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_465_condition (n a b : Nat) : Prop :=
  RightDifferent n a ((b * (L n b a)) % 2 ^ n) ((a * (L n b a)) % 2 ^ n)

instance (n a b : Nat) : Decidable (bv_term_small_rw_465_condition n a b) := by
  unfold bv_term_small_rw_465_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_465_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_465_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_465_solutions n p) := by
  unfold bv_term_small_rw_465_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_465_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_465 n s t ↔ bv_term_small_rw_465_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_465, bv_term_small_rw_465_condition, toNat_bvmul, toNat_left] using
    (right_different_iff s (bvmul t (bvshl t s)) (bvmul s (bvshl t s)))

theorem bv_term_small_rw_465_solutions_iff (n a b : Nat) :
    bv_term_small_rw_465_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_465 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_465_condition n) (bv_term_small_rw_465 n)
    (bv_term_small_rw_465_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_465_sat32 :
    bv_term_small_rw_465 32 (literal 32 1) (literal 32 65536) := by
  unfold bv_term_small_rw_465
  decide

end BV.QF_BV.Sat
