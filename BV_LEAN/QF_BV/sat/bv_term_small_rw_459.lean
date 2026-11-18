/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_459.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (right shifts by different counts):
The count (b+R(b,a)) mod P is compared with b. Wraparound can make it smaller, so the minimum of the two is used.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_459 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvadd t (bvlshr t s))) ≠ (bvlshr s t)

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_459_condition (n a b : Nat) : Prop :=
  RightDifferent n a ((b + (R n b a)) % 2 ^ n) b

instance (n a b : Nat) : Decidable (bv_term_small_rw_459_condition n a b) := by
  unfold bv_term_small_rw_459_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_459_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_459_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_459_solutions n p) := by
  unfold bv_term_small_rw_459_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_459_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_459 n s t ↔ bv_term_small_rw_459_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_459, bv_term_small_rw_459_condition, toNat_bvadd, toNat_right] using
    (right_different_iff s (bvadd t (bvlshr t s)) t)

theorem bv_term_small_rw_459_solutions_iff (n a b : Nat) :
    bv_term_small_rw_459_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_459 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_459_condition n) (bv_term_small_rw_459 n)
    (bv_term_small_rw_459_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_459_sat32 :
    bv_term_small_rw_459 32 (literal 32 27) (literal 32 4294967269) := by
  unfold bv_term_small_rw_459
  decide

end BV.QF_BV.Sat
