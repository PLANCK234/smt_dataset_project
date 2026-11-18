/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_313.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (bits missing from a mask):
The modular product is the right-shift count; the set bits of the quotient outside the mask a are exactly the mismatching bits.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_313 (n : Nat) (s t : BitVec n) : Prop :=
  (bvand s (bvlshr s (bvmul s t))) ≠ (bvlshr s (bvmul s t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_313_condition (n a b : Nat) : Prop :=
  (2 ^ n - 1 - a) &&& (R n a ((a * b) % 2 ^ n)) ≠ 0

instance (n a b : Nat) : Decidable (bv_term_small_rw_313_condition n a b) := by
  unfold bv_term_small_rw_313_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_313_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_313_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_313_solutions n p) := by
  unfold bv_term_small_rw_313_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_313_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_313 n s t ↔ bv_term_small_rw_313_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_313, bv_term_small_rw_313_condition, toNat_right, toNat_bvmul] using
    (mask_loss_iff s (bvlshr s (bvmul s t)))

theorem bv_term_small_rw_313_solutions_iff (n a b : Nat) :
    bv_term_small_rw_313_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_313 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_313_condition n) (bv_term_small_rw_313 n)
    (bv_term_small_rw_313_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_313_sat32 :
    bv_term_small_rw_313 32 (literal 32 4294967294) (literal 32 4294967295) := by
  unfold bv_term_small_rw_313
  decide

end BV.QF_BV.Sat
