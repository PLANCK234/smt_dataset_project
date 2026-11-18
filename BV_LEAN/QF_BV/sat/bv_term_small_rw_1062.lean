/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1062.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (difference inside and outside a mask):
A right shift masked by t is compared with a left shift masked by s. The masks differ, so both in-mask differences and out-of-mask target bits count.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1062 (n : Nat) (s t : BitVec n) : Prop :=
  (bvand t (bvlshr s (bvadd s s))) ≠ (bvand s (bvshl t (bvadd s s)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1062_condition (n a b : Nat) : Prop :=
  (b &&& ((R n a ((a + a) % 2 ^ n)) ^^^ (a &&& (L n b ((a + a) % 2 ^ n))))) ||| ((2 ^ n - 1 - b) &&& (a &&& (L n b ((a + a) % 2 ^ n)))) ≠ 0

instance (n a b : Nat) : Decidable (bv_term_small_rw_1062_condition n a b) := by
  unfold bv_term_small_rw_1062_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1062_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1062_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1062_solutions n p) := by
  unfold bv_term_small_rw_1062_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1062_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1062 n s t ↔ bv_term_small_rw_1062_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1062, bv_term_small_rw_1062_condition, toNat_bvadd, toNat_bvand, toNat_right, toNat_left] using
    (mask_target_different_iff t (bvlshr s (bvadd s s)) (bvand s (bvshl t (bvadd s s))))

theorem bv_term_small_rw_1062_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1062_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1062 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1062_condition n) (bv_term_small_rw_1062 n)
    (bv_term_small_rw_1062_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1062_sat32 :
    bv_term_small_rw_1062 32 (literal 32 2147483649) (literal 32 4294967295) := by
  unfold bv_term_small_rw_1062
  decide

end BV.QF_BV.Sat
