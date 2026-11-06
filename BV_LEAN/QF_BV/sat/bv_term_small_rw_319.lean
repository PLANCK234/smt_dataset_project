/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_319.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（共同掩码下的差异）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
先算 q=L(a,b)，左、右移结果只在 a 的置位上比较。未被 a 选中的差异对 SAT 无贡献。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_319 (n : Nat) (s t : BitVec n) : Prop :=
  (bvand s (bvshl s (bvshl s t))) ≠ (bvand s (bvlshr s (bvshl s t)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_319_condition (n a b : Nat) : Prop :=
  a &&& ((L n a (L n a b)) ^^^ (R n a (L n a b))) ≠ 0

instance (n a b : Nat) : Decidable (bv_term_small_rw_319_condition n a b) := by
  unfold bv_term_small_rw_319_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_319_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_319_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_319_solutions n p) := by
  unfold bv_term_small_rw_319_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_319_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_319 n s t ↔ bv_term_small_rw_319_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_319, bv_term_small_rw_319_condition, toNat_right, toNat_left] using
    (masked_different_iff s (bvshl s (bvshl s t)) (bvlshr s (bvshl s t)))

theorem bv_term_small_rw_319_solutions_iff (n a b : Nat) :
    bv_term_small_rw_319_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_319 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_319_condition n) (bv_term_small_rw_319 n)
    (bv_term_small_rw_319_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_319_sat32 :
    bv_term_small_rw_319 32 (literal 32 2147483663) (literal 32 1) := by
  unfold bv_term_small_rw_319
  decide

end BV.QF_BV.Sat
