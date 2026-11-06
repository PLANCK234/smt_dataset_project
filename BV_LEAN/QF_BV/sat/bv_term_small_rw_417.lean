/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_417.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（共同置位）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
先模加倍 a 作为 b 的左移量；SAT 要求其结果与原 a 有共同置位，内层非零本身不充分。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_417 (n : Nat) (s t : BitVec n) : Prop :=
  (bvand s (bvshl t (bvadd s s))) ≠ (literal n 0)

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_417_condition (n a b : Nat) : Prop :=
  a &&& (L n b ((a + a) % 2 ^ n)) ≠ 0

instance (n a b : Nat) : Decidable (bv_term_small_rw_417_condition n a b) := by
  unfold bv_term_small_rw_417_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_417_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_417_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_417_solutions n p) := by
  unfold bv_term_small_rw_417_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_417_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_417 n s t ↔ bv_term_small_rw_417_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_417, bv_term_small_rw_417_condition, toNat_bvadd, toNat_left] using
    (and_nonzero_iff s (bvshl t (bvadd s s)))

theorem bv_term_small_rw_417_solutions_iff (n a b : Nat) :
    bv_term_small_rw_417_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_417 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_417_condition n) (bv_term_small_rw_417 n)
    (bv_term_small_rw_417_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_417_sat32 :
    bv_term_small_rw_417 32 (literal 32 2147483648) (literal 32 4294967295) := by
  unfold bv_term_small_rw_417
  decide

end BV.QF_BV.Sat
