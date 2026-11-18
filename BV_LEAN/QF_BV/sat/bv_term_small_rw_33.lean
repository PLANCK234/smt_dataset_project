/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_33.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (modular product difference):
Let B=L(a,a); aB mod P is compared with B. B=0 and a=1 are not solutions, but B cannot be cancelled from the modular product. t is free.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_33 (n : Nat) (s t : BitVec n) : Prop :=
  (bvmul s (bvshl s s)) ≠ (bvshl s s)

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_33_condition (n a b : Nat) : Prop :=
  ResidueDifferent n (a * (L n a a)) (L n a a)

instance (n a b : Nat) : Decidable (bv_term_small_rw_33_condition n a b) := by
  unfold bv_term_small_rw_33_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_33_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_33_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_33_solutions n p) := by
  unfold bv_term_small_rw_33_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_33_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_33 n s t ↔ bv_term_small_rw_33_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_33, bv_term_small_rw_33_condition, toNat_left] using
    (mul_different_iff s (bvshl s s) (bvshl s s))

theorem bv_term_small_rw_33_solutions_iff (n a b : Nat) :
    bv_term_small_rw_33_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_33 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_33_condition n) (bv_term_small_rw_33 n)
    (bv_term_small_rw_33_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_33_sat32 :
    bv_term_small_rw_33 32 (literal 32 2) (literal 32 0) := by
  unfold bv_term_small_rw_33
  decide

end BV.QF_BV.Sat
