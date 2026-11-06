/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_322.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.SatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Sat
open SMT.BitVec

/- 数学分析（掩码内外差异）：
令 P=2^n、a=s.toNat、b=t.toNat，0≤a,b<P。
L n a q=(a*2^min(n,q)) mod P，R n a q=floor(a/2^min(n,q))。
左侧受 a 掩码限制，右侧不受限制。差异分成 a 内的 XOR 差异与 a 外的目标置位，两部分取 OR。
下列 condition 不含 BitVec；solutions 同时约束输入范围。
_iff 证明必要性与充分性；_solutions_iff 证明每个自然数解都能重建原始输入。
-/

/-- The original negated equality, generalized from width 32 to every n, including zero. -/
def bv_term_small_rw_322 (n : Nat) (s t : BitVec n) : Prop :=
  (bvand s (bvlshr s (bvlshr t s))) ≠ (bvlshr s (bvneg (bvlshr t s)))

/-- Exact arithmetic / bit-mask membership criterion, not just a SAT witness. -/
def bv_term_small_rw_322_condition (n a b : Nat) : Prop :=
  (a &&& ((R n a (R n b a)) ^^^ (R n a ((2 ^ n - (R n b a)) % 2 ^ n)))) ||| ((2 ^ n - 1 - a) &&& (R n a ((2 ^ n - (R n b a)) % 2 ^ n))) ≠ 0

instance (n a b : Nat) : Decidable (bv_term_small_rw_322_condition n a b) := by
  unfold bv_term_small_rw_322_condition
  infer_instance

/-- The complete solution set as bounded natural pairs. -/
def bv_term_small_rw_322_solutions (n : Nat) : Nat × Nat → Prop :=
  SolutionSet n (bv_term_small_rw_322_condition n)

instance (n : Nat) (p : Nat × Nat) : Decidable (bv_term_small_rw_322_solutions n p) := by
  unfold bv_term_small_rw_322_solutions SolutionSet
  infer_instance

theorem bv_term_small_rw_322_iff (n : Nat) (s t : BitVec n) :
    bv_term_small_rw_322 n s t ↔ bv_term_small_rw_322_condition n s.toNat t.toNat := by
  simpa only [bv_term_small_rw_322, bv_term_small_rw_322_condition, toNat_right, toNat_bvneg] using
    (mask_target_different_iff s (bvlshr s (bvlshr t s)) (bvlshr s (bvneg (bvlshr t s))))

theorem bv_term_small_rw_322_solutions_iff (n a b : Nat) :
    bv_term_small_rw_322_solutions n (a, b) ↔
      ∃ s t : BitVec n, s.toNat = a ∧ t.toNat = b ∧ bv_term_small_rw_322 n s t :=
  solutionSet_iff_exists (bv_term_small_rw_322_condition n) (bv_term_small_rw_322 n)
    (bv_term_small_rw_322_iff n) a b

/-- A concrete witness for the source's 32-bit SAT status; checked by kernel reduction. -/
theorem bv_term_small_rw_322_sat32 :
    bv_term_small_rw_322 32 (literal 32 3) (literal 32 8) := by
  unfold bv_term_small_rw_322
  decide

end BV.QF_BV.Sat
