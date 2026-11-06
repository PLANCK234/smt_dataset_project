/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_158.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（顺序左移的计数重叠）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
顺序左移的计数和等于 OR 加 AND；AND 非零且按 OR 左移后仍非零，恰好构成解。正次数左移没有非零不动点。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_158 (n : Nat) (s t : BitVec n) : Prop :=
  (bvshl (bvshl s s) t) ≠ (bvshl s (bvor s t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_158_condition (n a b : Nat) : Prop :=
  SequentialLeftDifferent n a a b

instance (n a b : Nat) : Decidable (bv_term_small_rw_158_condition n a b) := by
  unfold bv_term_small_rw_158_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_158_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_158_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_158_solutions n p) := by
  unfold bv_term_small_rw_158_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_158_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_158 n s t ↔ bv_term_small_rw_158_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_158, bv_term_small_rw_158_condition] using
    (sequential_left_different_iff s s t)

theorem bv_term_small_rw_158_solutions_iff (n a b : Nat) :
    bv_term_small_rw_158_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_158 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_158_condition n) (bv_term_small_rw_158 n)
    (bv_term_small_rw_158_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_158_sat32 :
    bv_term_small_rw_158 32 (literal 32 1) (literal 32 1) := by
  unfold bv_term_small_rw_158
  decide

end BV.QF_BV.Sat
