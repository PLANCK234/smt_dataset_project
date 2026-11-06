/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_317.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（不同计数右移）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
两种内层移位分别参与模加法生成外层计数；比较最终计数，不把加法前的大小关系直接带过回绕。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_317 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvadd s (bvshl s t))) ≠ (bvlshr s (bvadd s (bvlshr s t)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_317_condition (n a b : Nat) : Prop :=
  RightDifferent n a ((a + (L n a b)) % 2 ^ n) ((a + (R n a b)) % 2 ^ n)

instance (n a b : Nat) : Decidable (bv_term_small_rw_317_condition n a b) := by
  unfold bv_term_small_rw_317_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_317_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_317_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_317_solutions n p) := by
  unfold bv_term_small_rw_317_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_317_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_317 n s t ↔ bv_term_small_rw_317_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_317, bv_term_small_rw_317_condition, toNat_bvadd, toNat_right, toNat_left] using
    (right_different_iff s (bvadd s (bvshl s t)) (bvadd s (bvlshr s t)))

theorem bv_term_small_rw_317_solutions_iff (n a b : Nat) :
    bv_term_small_rw_317_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_317 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_317_condition n) (bv_term_small_rw_317 n)
    (bv_term_small_rw_317_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_317_sat32 :
    bv_term_small_rw_317 32 (literal 32 4294967295) (literal 32 27) := by
  unfold bv_term_small_rw_317
  decide

end BV.QF_BV.Sat
