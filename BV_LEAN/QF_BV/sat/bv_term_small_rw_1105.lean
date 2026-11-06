/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1105.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（模乘积差）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
共同移位量是 c=L(b,a)，两商随后分别乘 b、a 并模 P；不能直接交换乘法与右移，用模差刻画失配。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1105 (n : Nat) (s t : BitVec n) : Prop :=
  (bvmul t (bvlshr s (bvshl t s))) ≠ (bvmul s (bvlshr t (bvshl t s)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1105_condition (n a b : Nat) : Prop :=
  ResidueDifferent n (b * (R n a (L n b a))) ((a * (R n b (L n b a))) % 2 ^ n)

instance (n a b : Nat) : Decidable (bv_term_small_rw_1105_condition n a b) := by
  unfold bv_term_small_rw_1105_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1105_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1105_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1105_solutions n p) := by
  unfold bv_term_small_rw_1105_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1105_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1105 n s t ↔ bv_term_small_rw_1105_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1105, bv_term_small_rw_1105_condition, toNat_right, toNat_bvmul, toNat_left] using
    (mul_different_iff t (bvlshr s (bvshl t s)) (bvmul s (bvlshr t (bvshl t s))))

theorem bv_term_small_rw_1105_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1105_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1105 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1105_condition n) (bv_term_small_rw_1105 n)
    (bv_term_small_rw_1105_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1105_sat32 :
    bv_term_small_rw_1105 32 (literal 32 1) (literal 32 2147483649) := by
  unfold bv_term_small_rw_1105
  decide

end BV.QF_BV.Sat
