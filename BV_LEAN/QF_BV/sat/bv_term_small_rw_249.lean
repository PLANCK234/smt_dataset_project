/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_249.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（不同计数右移）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
两个计数分别为左移值、右移值的有限补码；补码可反转计数大小，故阈值必须使用 min(q,r)。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_249 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvnot (bvshl s t))) ≠ (bvlshr s (bvnot (bvlshr s t)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_249_condition (n a b : Nat) : Prop :=
  RightDifferent n a (2 ^ n - 1 - (L n a b)) (2 ^ n - 1 - (R n a b))

instance (n a b : Nat) : Decidable (bv_term_small_rw_249_condition n a b) := by
  unfold bv_term_small_rw_249_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_249_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_249_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_249_solutions n p) := by
  unfold bv_term_small_rw_249_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_249_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_249 n s t ↔ bv_term_small_rw_249_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_249, bv_term_small_rw_249_condition, toNat_right, toNat_bvnot, toNat_left] using
    (right_different_iff s (bvnot (bvshl s t)) (bvnot (bvlshr s t)))

theorem bv_term_small_rw_249_solutions_iff (n a b : Nat) :
    bv_term_small_rw_249_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_249 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_249_condition n) (bv_term_small_rw_249 n)
    (bv_term_small_rw_249_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_249_sat32 :
    bv_term_small_rw_249 32 (literal 32 4294967295) (literal 32 1) := by
  unfold bv_term_small_rw_249
  decide

end BV.QF_BV.Sat
