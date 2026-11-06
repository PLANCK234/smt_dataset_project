/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_340.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（不同计数右移）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
OR 与加法的差异来自共同置位引起的进位，并可能回绕；最终以两计数和 a 的较小阈值判断。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_340 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr s (bvor t (bvnot s))) ≠ (bvlshr s (bvadd t (bvnot s)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_340_condition (n a b : Nat) : Prop :=
  RightDifferent n a (b ||| (2 ^ n - 1 - a)) ((b + (2 ^ n - 1 - a)) % 2 ^ n)

instance (n a b : Nat) : Decidable (bv_term_small_rw_340_condition n a b) := by
  unfold bv_term_small_rw_340_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_340_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_340_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_340_solutions n p) := by
  unfold bv_term_small_rw_340_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_340_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_340 n s t ↔ bv_term_small_rw_340_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_340, bv_term_small_rw_340_condition, toNat_bvadd, toNat_bvnot, toNat_bvor] using
    (right_different_iff s (bvor t (bvnot s)) (bvadd t (bvnot s)))

theorem bv_term_small_rw_340_solutions_iff (n a b : Nat) :
    bv_term_small_rw_340_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_340 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_340_condition n) (bv_term_small_rw_340 n)
    (bv_term_small_rw_340_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_340_sat32 :
    bv_term_small_rw_340 32 (literal 32 1) (literal 32 2) := by
  unfold bv_term_small_rw_340
  decide

end BV.QF_BV.Sat
