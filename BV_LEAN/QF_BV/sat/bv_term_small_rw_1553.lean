/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1553.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（商区间补集）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
左侧模乘积 (a AND b)b 的右移与 b 掩码下模平方 b 的右移比较；算出目标后用商区间补集，保留乘法进位。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1553 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr (bvmul (bvand s t) t) t) ≠ (bvand t (bvlshr (bvmul t t) t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1553_condition (n a b : Nat) : Prop :=
  QuotientDifferent n (((a &&& b) * b) % 2 ^ n) b (b &&& (R n ((b * b) % 2 ^ n) b))

instance (n a b : Nat) : Decidable (bv_term_small_rw_1553_condition n a b) := by
  unfold bv_term_small_rw_1553_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1553_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1553_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1553_solutions n p) := by
  unfold bv_term_small_rw_1553_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1553_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1553 n s t ↔ bv_term_small_rw_1553_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1553, bv_term_small_rw_1553_condition, toNat_bvand, toNat_right, toNat_bvmul] using
    (quotient_different_iff (bvmul (bvand s t) t) t (bvand t (bvlshr (bvmul t t) t)))

theorem bv_term_small_rw_1553_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1553_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1553 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1553_condition n) (bv_term_small_rw_1553 n)
    (bv_term_small_rw_1553_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1553_sat32 :
    bv_term_small_rw_1553 32 (literal 32 0) (literal 32 3) := by
  unfold bv_term_small_rw_1553
  decide

end BV.QF_BV.Sat
