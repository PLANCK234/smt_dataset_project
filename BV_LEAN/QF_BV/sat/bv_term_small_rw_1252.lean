/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1252.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- Analysis (outside a quotient interval):
The left side is a^2 mod P shifted right by a OR b; the right side is the masked right shift of the square by a. With the target fixed, solutions lie outside its quotient interval.
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1252 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr (bvmul s s) (bvor s t)) ≠ (bvand s (bvlshr (bvmul s s) s))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1252_condition (n a b : Nat) : Prop :=
  QuotientDifferent n ((a * a) % 2 ^ n) (a ||| b) (a &&& (R n ((a * a) % 2 ^ n) a))

instance (n a b : Nat) : Decidable (bv_term_small_rw_1252_condition n a b) := by
  unfold bv_term_small_rw_1252_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1252_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1252_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1252_solutions n p) := by
  unfold bv_term_small_rw_1252_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1252_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1252 n s t ↔ bv_term_small_rw_1252_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1252, bv_term_small_rw_1252_condition, toNat_bvand, toNat_right, toNat_bvmul, toNat_bvor] using
    (quotient_different_iff (bvmul s s) (bvor s t) (bvand s (bvlshr (bvmul s s) s)))

theorem bv_term_small_rw_1252_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1252_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1252 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1252_condition n) (bv_term_small_rw_1252 n)
    (bv_term_small_rw_1252_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1252_sat32 :
    bv_term_small_rw_1252 32 (literal 32 2) (literal 32 0) := by
  unfold bv_term_small_rw_1252
  decide

end BV.QF_BV.Sat
