/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1553.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (outside a quotient interval):
The right shift of (a AND b)*b mod P is compared with the masked right shift of b^2 mod P. With the target fixed, solutions lie outside its quotient interval; multiplication carries are preserved.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1553 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr (bvmul (bvand s t) t) t) ≠ (bvand t (bvlshr (bvmul t t) t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1553_condition (n a b : Nat) : Prop :=
  QuotientDifferent n (((a &&& b) * b) % 2 ^ n) b (b &&& (R n ((b * b) % 2 ^ n) b))

instance (n a b : Nat) : Decidable (bv_term_small_rw_1553_condition n a b) := by
  unfold bv_term_small_rw_1553_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1553_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1553_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1553_solutions n p) := by
  unfold bv_term_small_rw_1553_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1553_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1553 n s t ↔ bv_term_small_rw_1553_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1553, bv_term_small_rw_1553_condition, toNat_bvand, toNat_right, toNat_bvmul] using
    (quotient_different_iff (bvmul (bvand s t) t) t (bvand t (bvlshr (bvmul t t) t)))

theorem bv_term_small_rw_1553_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1553_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1553 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1553_condition n) (bv_term_small_rw_1553 n)
    (bv_term_small_rw_1553_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1553_sat32 :
    bv_term_small_rw_1553 32 (literal 32 0) (literal 32 3) := by
  unfold bv_term_small_rw_1553
  decide

end BV.QF_BV.Sat
