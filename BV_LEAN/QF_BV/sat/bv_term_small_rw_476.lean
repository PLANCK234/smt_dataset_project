/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_476.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (right shifts by different counts):
The counts are b OR (2b mod P) and 3b mod P. The OR is not an addition, and the outer threshold is checked after wraparound.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_476 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvor t (bvadd t t))) ≠ (bvlshr s (bvadd t (bvadd t t)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_476_condition (n a b : Nat) : Prop :=
  RightDifferent n a (b ||| ((b + b) % 2 ^ n)) ((b + ((b + b) % 2 ^ n)) % 2 ^ n)

instance (n a b : Nat) : Decidable (bv_term_small_rw_476_condition n a b) := by
  unfold bv_term_small_rw_476_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_476_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_476_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_476_solutions n p) := by
  unfold bv_term_small_rw_476_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_476_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_476 n s t ↔ bv_term_small_rw_476_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_476, bv_term_small_rw_476_condition, toNat_bvadd, toNat_bvor] using
    (right_different_iff s (bvor t (bvadd t t)) (bvadd t (bvadd t t)))

theorem bv_term_small_rw_476_solutions_iff (n a b : Nat) :
    bv_term_small_rw_476_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_476 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_476_condition n) (bv_term_small_rw_476 n)
    (bv_term_small_rw_476_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_476_sat32 :
    bv_term_small_rw_476 32 (literal 32 4294967295) (literal 32 3) := by
  unfold bv_term_small_rw_476
  decide

end BV.QF_BV.Sat
