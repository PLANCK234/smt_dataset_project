/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1110.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (modular product difference):
Masking before multiplying by b carries differently from masking after; the modular difference condition tests the left product against the right target.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1110 (n : Nat) (s t : BitVec n) : Prop :=
  (bvmul t (bvand s (bvshl t t))) ≠ (bvand s (bvmul t (bvshl t t)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1110_condition (n a b : Nat) : Prop :=
  ResidueDifferent n (b * (a &&& (L n b b))) (a &&& ((b * (L n b b)) % 2 ^ n))

instance (n a b : Nat) : Decidable (bv_term_small_rw_1110_condition n a b) := by
  unfold bv_term_small_rw_1110_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1110_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1110_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1110_solutions n p) := by
  unfold bv_term_small_rw_1110_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1110_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1110 n s t ↔ bv_term_small_rw_1110_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1110, bv_term_small_rw_1110_condition, toNat_bvand, toNat_bvmul, toNat_left] using
    (mul_different_iff t (bvand s (bvshl t t)) (bvand s (bvmul t (bvshl t t))))

theorem bv_term_small_rw_1110_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1110_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1110 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1110_condition n) (bv_term_small_rw_1110 n)
    (bv_term_small_rw_1110_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1110_sat32 :
    bv_term_small_rw_1110 32 (literal 32 8) (literal 32 2) := by
  unfold bv_term_small_rw_1110
  decide

end BV.QF_BV.Sat
