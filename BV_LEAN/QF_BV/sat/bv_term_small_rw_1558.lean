/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1558.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（顺序左移的计数重叠）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
共同基数 X=R(a,b)。解恰当 a AND b 非零且 X 按 a OR b 左移仍非零；X=0 的所有输入自然被排除。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1558 (n : Nat) (s t : BitVec n) : Prop :=
  (bvshl (bvshl (bvlshr s t) s) t) ≠ (bvshl (bvlshr s t) (bvor s t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1558_condition (n a b : Nat) : Prop :=
  SequentialLeftDifferent n (R n a b) a b

instance (n a b : Nat) : Decidable (bv_term_small_rw_1558_condition n a b) := by
  unfold bv_term_small_rw_1558_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1558_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1558_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1558_solutions n p) := by
  unfold bv_term_small_rw_1558_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1558_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1558 n s t ↔ bv_term_small_rw_1558_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1558, bv_term_small_rw_1558_condition, toNat_right] using
    (sequential_left_different_iff (bvlshr s t) s t)

theorem bv_term_small_rw_1558_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1558_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1558 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1558_condition n) (bv_term_small_rw_1558 n)
    (bv_term_small_rw_1558_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1558_sat32 :
    bv_term_small_rw_1558 32 (literal 32 3) (literal 32 1) := by
  unfold bv_term_small_rw_1558
  decide

end BV.QF_BV.Sat
