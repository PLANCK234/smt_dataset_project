/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1331.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (outside a quotient interval):
a AND b shifted right by q=R(a,b) is compared with the masked right shift of b; the target interval handles masking and shifting not commuting.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1331 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr (bvand s t) (bvlshr s t)) ≠ (bvand s (bvlshr t (bvlshr s t)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1331_condition (n a b : Nat) : Prop :=
  QuotientDifferent n (a &&& b) (R n a b) (a &&& (R n b (R n a b)))

instance (n a b : Nat) : Decidable (bv_term_small_rw_1331_condition n a b) := by
  unfold bv_term_small_rw_1331_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1331_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1331_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1331_solutions n p) := by
  unfold bv_term_small_rw_1331_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1331_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1331 n s t ↔ bv_term_small_rw_1331_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1331, bv_term_small_rw_1331_condition, toNat_bvand, toNat_right] using
    (quotient_different_iff (bvand s t) (bvlshr s t) (bvand s (bvlshr t (bvlshr s t))))

theorem bv_term_small_rw_1331_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1331_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1331 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1331_condition n) (bv_term_small_rw_1331 n)
    (bv_term_small_rw_1331_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1331_sat32 :
    bv_term_small_rw_1331 32 (literal 32 5) (literal 32 2) := by
  unfold bv_term_small_rw_1331
  decide

end BV.QF_BV.Sat
