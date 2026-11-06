/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1393.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（商区间补集）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
左侧先左移 a 再按 a OR b 右移，右侧为 a 掩码下 b 自左移后的右移；以右侧目标的商区间比较左侧。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1393 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr (bvshl s t) (bvor s t)) ≠ (bvand s (bvlshr (bvshl t t) s))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1393_condition (n a b : Nat) : Prop :=
  QuotientDifferent n (L n a b) (a ||| b) (a &&& (R n (L n b b) a))

instance (n a b : Nat) : Decidable (bv_term_small_rw_1393_condition n a b) := by
  unfold bv_term_small_rw_1393_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1393_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1393_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1393_solutions n p) := by
  unfold bv_term_small_rw_1393_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1393_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1393 n s t ↔ bv_term_small_rw_1393_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1393, bv_term_small_rw_1393_condition, toNat_bvand, toNat_right, toNat_bvor, toNat_left] using
    (quotient_different_iff (bvshl s t) (bvor s t) (bvand s (bvlshr (bvshl t t) s)))

theorem bv_term_small_rw_1393_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1393_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1393 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1393_condition n) (bv_term_small_rw_1393 n)
    (bv_term_small_rw_1393_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1393_sat32 :
    bv_term_small_rw_1393 32 (literal 32 1) (literal 32 3) := by
  unfold bv_term_small_rw_1393
  decide

end BV.QF_BV.Sat
