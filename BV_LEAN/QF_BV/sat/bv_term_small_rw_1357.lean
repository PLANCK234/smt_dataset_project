/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1357.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（顺序右移自然和）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
左侧计数是 b+((a+b) mod P) 的自然和，右侧是 (a+(2b mod P)) mod P；两种加法的位置必须严格区分。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_1357 (n : Nat) (s t : BitVec n) : Prop :=
  (bvlshr (bvlshr s t) (bvadd s t)) ≠ (bvlshr s (bvadd s (bvadd t t)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_1357_condition (n a b : Nat) : Prop :=
  RightDifferent n a (b + ((a + b) % 2 ^ n)) ((a + ((b + b) % 2 ^ n)) % 2 ^ n)

instance (n a b : Nat) : Decidable (bv_term_small_rw_1357_condition n a b) := by
  unfold bv_term_small_rw_1357_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_1357_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_1357_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_1357_solutions n p) := by
  unfold bv_term_small_rw_1357_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_1357_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_1357 n s t ↔ bv_term_small_rw_1357_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_1357, bv_term_small_rw_1357_condition, toNat_bvadd] using
    (nested_right_different_iff s t (bvadd s t) (bvadd s (bvadd t t)))

theorem bv_term_small_rw_1357_solutions_iff (n a b : Nat) :
    bv_term_small_rw_1357_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_1357 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_1357_condition n) (bv_term_small_rw_1357 n)
    (bv_term_small_rw_1357_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_1357_sat32 :
    bv_term_small_rw_1357 32 (literal 32 2) (literal 32 4294967295) := by
  unfold bv_term_small_rw_1357
  decide

end BV.QF_BV.Sat
