/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_472.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (right shifts by different counts):
With c=L(b,a), a is shifted right by b OR c and by (b+c) mod P; carries and wraparound stay in the exact counts.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_472 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvor t (bvshl t s))) ≠ (bvlshr s (bvadd t (bvshl t s)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_472_condition (n a b : Nat) : Prop :=
  RightDifferent n a (b ||| (L n b a)) ((b + (L n b a)) % 2 ^ n)

instance (n a b : Nat) : Decidable (bv_term_small_rw_472_condition n a b) := by
  unfold bv_term_small_rw_472_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_472_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_472_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_472_solutions n p) := by
  unfold bv_term_small_rw_472_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_472_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_472 n s t ↔ bv_term_small_rw_472_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_472, bv_term_small_rw_472_condition, toNat_bvadd, toNat_bvor, toNat_left] using
    (right_different_iff s (bvor t (bvshl t s)) (bvadd t (bvshl t s)))

theorem bv_term_small_rw_472_solutions_iff (n a b : Nat) :
    bv_term_small_rw_472_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_472 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_472_condition n) (bv_term_small_rw_472 n)
    (bv_term_small_rw_472_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_472_sat32 :
    bv_term_small_rw_472 32 (literal 32 30) (literal 32 2147483650) := by
  unfold bv_term_small_rw_472
  decide

end BV.QF_BV.Sat
