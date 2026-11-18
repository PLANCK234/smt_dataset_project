/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_299.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (nonzero right-shift threshold):
The tripled value is reduced mod P before use as a count; SAT iff a reaches its power-of-two threshold. t is free.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_299 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvadd s (bvadd s s))) ≠ (literal n 0)

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_299_condition (n a b : Nat) : Prop :=
  RightNonzero n a ((a + ((a + a) % 2 ^ n)) % 2 ^ n)

instance (n a b : Nat) : Decidable (bv_term_small_rw_299_condition n a b) := by
  unfold bv_term_small_rw_299_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_299_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_299_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_299_solutions n p) := by
  unfold bv_term_small_rw_299_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_299_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_299 n s t ↔ bv_term_small_rw_299_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_299, bv_term_small_rw_299_condition, toNat_bvadd] using
    (right_nonzero_iff s (bvadd s (bvadd s s)))

theorem bv_term_small_rw_299_solutions_iff (n a b : Nat) :
    bv_term_small_rw_299_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_299 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_299_condition n) (bv_term_small_rw_299 n)
    (bv_term_small_rw_299_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_299_sat32 :
    bv_term_small_rw_299 32 (literal 32 1431655766) (literal 32 0) := by
  unfold bv_term_small_rw_299
  decide

end BV.QF_BV.Sat
