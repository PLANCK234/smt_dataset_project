/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_366.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（左右移整除）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
q=b(P-1-b) mod P 是补码乘积；外层 a 独立，解集不能按 q 的数值区间单独刻画。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_366 (n : Nat) (s t : BitVec n) : Prop :=
  (bvshl s (bvmul t (bvnot t))) ≠ (bvlshr s (bvmul t (bvnot t)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_366_condition (n a b : Nat) : Prop :=
  ShiftDifferent n a ((b * (2 ^ n - 1 - b)) % 2 ^ n)

instance (n a b : Nat) : Decidable (bv_term_small_rw_366_condition n a b) := by
  unfold bv_term_small_rw_366_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_366_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_366_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_366_solutions n p) := by
  unfold bv_term_small_rw_366_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_366_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_366 n s t ↔ bv_term_small_rw_366_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_366, bv_term_small_rw_366_condition, toNat_bvmul, toNat_bvnot] using
    (shift_different_iff s (bvmul t (bvnot t)))

theorem bv_term_small_rw_366_solutions_iff (n a b : Nat) :
    bv_term_small_rw_366_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_366 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_366_condition n) (bv_term_small_rw_366 n)
    (bv_term_small_rw_366_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_366_sat32 :
    bv_term_small_rw_366 32 (literal 32 1301626122) (literal 32 2951684490) := by
  unfold bv_term_small_rw_366
  decide

end BV.QF_BV.Sat
