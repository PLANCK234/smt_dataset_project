/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_160.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (outside a quotient interval):
Let U=ab mod P and V=b*R(a,b) mod P. The right shift of U equals V iff U lies in the power-of-two quotient interval of V; solutions are its complement.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_160 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr (bvmul s t) t) ≠ (bvmul t (bvlshr s t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_160_condition (n a b : Nat) : Prop :=
  QuotientDifferent n ((a * b) % 2 ^ n) b ((b * (R n a b)) % 2 ^ n)

instance (n a b : Nat) : Decidable (bv_term_small_rw_160_condition n a b) := by
  unfold bv_term_small_rw_160_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_160_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_160_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_160_solutions n p) := by
  unfold bv_term_small_rw_160_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_160_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_160 n s t ↔ bv_term_small_rw_160_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_160, bv_term_small_rw_160_condition, toNat_right, toNat_bvmul] using
    (quotient_different_iff (bvmul s t) t (bvmul t (bvlshr s t)))

theorem bv_term_small_rw_160_solutions_iff (n a b : Nat) :
    bv_term_small_rw_160_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_160 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_160_condition n) (bv_term_small_rw_160 n)
    (bv_term_small_rw_160_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_160_sat32 :
    bv_term_small_rw_160 32 (literal 32 2) (literal 32 2) := by
  unfold bv_term_small_rw_160
  decide

end BV.QF_BV.Sat
