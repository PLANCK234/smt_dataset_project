/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_311.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（掩码缺失位）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
设 X=R(a,(a+b) mod P)。原断言要求 X 有至少一个置位落在 a 的零位上；缺失位掩码 (~a)&X 完整刻画解集。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_311 (n : Nat) (s t : BitVec n) : Prop :=
  (bvand s (bvlshr s (bvadd s t))) ≠ (bvlshr s (bvadd s t))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_311_condition (n a b : Nat) : Prop :=
  (2 ^ n - 1 - a) &&& (R n a ((a + b) % 2 ^ n)) ≠ 0

instance (n a b : Nat) : Decidable (bv_term_small_rw_311_condition n a b) := by
  unfold bv_term_small_rw_311_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_311_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_311_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_311_solutions n p) := by
  unfold bv_term_small_rw_311_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_311_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_311 n s t ↔ bv_term_small_rw_311_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_311, bv_term_small_rw_311_condition, toNat_bvadd, toNat_right] using
    (mask_loss_iff s (bvlshr s (bvadd s t)))

theorem bv_term_small_rw_311_solutions_iff (n a b : Nat) :
    bv_term_small_rw_311_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_311 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_311_condition n) (bv_term_small_rw_311 n)
    (bv_term_small_rw_311_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_311_sat32 :
    bv_term_small_rw_311 32 (literal 32 2) (literal 32 4294967295) := by
  unfold bv_term_small_rw_311
  decide

end BV.QF_BV.Sat
