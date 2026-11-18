/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_337.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (bits missing from a mask):
b is shifted right by the complement of a; the AND changes the quotient iff it has a set bit at a zero bit of a.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_337 (n : Nat) (s t : BitVec n) : Prop :=
  (bvand s (bvlshr t (bvnot s))) ≠ (bvlshr t (bvnot s))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_337_condition (n a b : Nat) : Prop :=
  (2 ^ n - 1 - a) &&& (R n b (2 ^ n - 1 - a)) ≠ 0

instance (n a b : Nat) : Decidable (bv_term_small_rw_337_condition n a b) := by
  unfold bv_term_small_rw_337_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_337_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_337_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_337_solutions n p) := by
  unfold bv_term_small_rw_337_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_337_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_337 n s t ↔ bv_term_small_rw_337_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_337, bv_term_small_rw_337_condition, toNat_right, toNat_bvnot] using
    (mask_loss_iff s (bvlshr t (bvnot s)))

theorem bv_term_small_rw_337_solutions_iff (n a b : Nat) :
    bv_term_small_rw_337_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_337 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_337_condition n) (bv_term_small_rw_337 n)
    (bv_term_small_rw_337_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_337_sat32 :
    bv_term_small_rw_337 32 (literal 32 4294967294) (literal 32 2) := by
  unfold bv_term_small_rw_337
  decide

end BV.QF_BV.Sat
