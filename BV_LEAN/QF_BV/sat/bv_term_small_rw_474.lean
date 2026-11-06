/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_474.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（共同置位）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
模加倍 b 后右移 b，再与 a 取交；解要求这个右移商至少有一个被 a 选中的置位。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_474 (n : Nat) (s t : BitVec n) : Prop :=
  (bvand s (bvlshr t (bvadd t t))) ≠ (literal n 0)

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_474_condition (n a b : Nat) : Prop :=
  a &&& (R n b ((b + b) % 2 ^ n)) ≠ 0

instance (n a b : Nat) : Decidable (bv_term_small_rw_474_condition n a b) := by
  unfold bv_term_small_rw_474_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_474_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_474_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_474_solutions n p) := by
  unfold bv_term_small_rw_474_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_474_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_474 n s t ↔ bv_term_small_rw_474_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_474, bv_term_small_rw_474_condition, toNat_bvadd, toNat_right] using
    (and_nonzero_iff s (bvlshr t (bvadd t t)))

theorem bv_term_small_rw_474_solutions_iff (n a b : Nat) :
    bv_term_small_rw_474_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_474 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_474_condition n) (bv_term_small_rw_474 n)
    (bv_term_small_rw_474_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_474_sat32 :
    bv_term_small_rw_474 32 (literal 32 4294967295) (literal 32 2147483648) := by
  unfold bv_term_small_rw_474
  decide

end BV.QF_BV.Sat
