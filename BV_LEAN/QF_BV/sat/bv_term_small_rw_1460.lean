/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1460.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（商区间补集）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
左边模乘积 a(a AND b) 按 a 右移，右边模乘积 ab 按 a OR b 右移；两个分母不同，用右侧商作为目标区间。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1460 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr (bvmul s (bvand s t)) s) ≠ (bvlshr (bvmul s t) (bvor s t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1460_condition (n a b : Nat) : Prop :=
  QuotientDifferent n ((a * (a &&& b)) % 2 ^ n) a (R n ((a * b) % 2 ^ n) (a ||| b))

instance (n a b : Nat) : Decidable (bv_term_small_rw_1460_condition n a b) := by
  unfold bv_term_small_rw_1460_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1460_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1460_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1460_solutions n p) := by
  unfold bv_term_small_rw_1460_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1460_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1460 n s t ↔ bv_term_small_rw_1460_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1460, bv_term_small_rw_1460_condition, toNat_bvand, toNat_right, toNat_bvmul, toNat_bvor] using
    (quotient_different_iff (bvmul s (bvand s t)) s (bvlshr (bvmul s t) (bvor s t)))

theorem bv_term_small_rw_1460_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1460_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1460 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1460_condition n) (bv_term_small_rw_1460 n)
    (bv_term_small_rw_1460_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1460_sat32 :
    bv_term_small_rw_1460 32 (literal 32 2) (literal 32 3) := by
  unfold bv_term_small_rw_1460
  decide

end BV.QF_BV.Sat
