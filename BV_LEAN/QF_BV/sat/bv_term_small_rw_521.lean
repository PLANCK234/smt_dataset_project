/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_521.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（共同掩码下的差异）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
两侧共享 a 掩码与基数 b，但内层计数分别为 L(b,b) 和 L(a,b)；被 a 选中的 XOR 差异才产生解。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_521 (n : Nat) (s t : BitVec n) : Prop :=
  (bvand s (bvlshr t (bvshl t t))) ≠ (bvand s (bvlshr t (bvshl s t)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_521_condition (n a b : Nat) : Prop :=
  a &&& ((R n b (L n b b)) ^^^ (R n b (L n a b))) ≠ 0

instance (n a b : Nat) : Decidable (bv_term_small_rw_521_condition n a b) := by
  unfold bv_term_small_rw_521_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_521_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_521_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_521_solutions n p) := by
  unfold bv_term_small_rw_521_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_521_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_521 n s t ↔ bv_term_small_rw_521_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_521, bv_term_small_rw_521_condition, toNat_right, toNat_left] using
    (masked_different_iff s (bvlshr t (bvshl t t)) (bvlshr t (bvshl s t)))

theorem bv_term_small_rw_521_solutions_iff (n a b : Nat) :
    bv_term_small_rw_521_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_521 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_521_condition n) (bv_term_small_rw_521 n)
    (bv_term_small_rw_521_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_521_sat32 :
    bv_term_small_rw_521 32 (literal 32 2) (literal 32 31) := by
  unfold bv_term_small_rw_521
  decide

end BV.QF_BV.Sat
