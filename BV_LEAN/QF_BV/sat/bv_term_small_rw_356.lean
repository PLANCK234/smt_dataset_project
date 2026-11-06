/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_356.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（不同计数右移）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
左计数为 b 按其模负号右移的商，右计数为 a 按 b 的补码左移的值；共同外层输入使右移判据适用。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_356 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvlshr t (bvneg t))) ≠ (bvlshr s (bvshl s (bvnot t)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_356_condition (n a b : Nat) : Prop :=
  RightDifferent n a (R n b ((2 ^ n - b) % 2 ^ n)) (L n a (2 ^ n - 1 - b))

instance (n a b : Nat) : Decidable (bv_term_small_rw_356_condition n a b) := by
  unfold bv_term_small_rw_356_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_356_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_356_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_356_solutions n p) := by
  unfold bv_term_small_rw_356_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_356_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_356 n s t ↔ bv_term_small_rw_356_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_356, bv_term_small_rw_356_condition, toNat_right, toNat_bvneg, toNat_bvnot, toNat_left] using
    (right_different_iff s (bvlshr t (bvneg t)) (bvshl s (bvnot t)))

theorem bv_term_small_rw_356_solutions_iff (n a b : Nat) :
    bv_term_small_rw_356_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_356 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_356_condition n) (bv_term_small_rw_356 n)
    (bv_term_small_rw_356_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_356_sat32 :
    bv_term_small_rw_356 32 (literal 32 1) (literal 32 4294967264) := by
  unfold bv_term_small_rw_356
  decide

end BV.QF_BV.Sat
