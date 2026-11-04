/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_477.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.ExactConditions
import LEMMAS_learned.BitVec.Shift.Characterization
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvshl_eq_bvlshr_bvlshr_of_lt_or_le (x y z : BitVec n)
    (h : y.toNat < 2 ^ z.toNat ∨ n * 2 ^ z.toNat ≤ y.toNat) :
    bvshl x (bvlshr y z) = bvlshr x (bvlshr y z) := by
  apply (bvshl_eq_bvlshr_forall_iff _).mpr _ x
  rw [toNat_bvlshr]
  rcases h with h | h
  · exact Or.inl (Nat.div_eq_of_lt h)
  · exact Or.inr ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr h)

def bv_term_small_rw_477 : Prop :=
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvlshr t (bvmul t t))) = (bvlshr s (bvlshr t (bvmul t t)))

theorem bv_term_small_rw_477_counterexample : ¬ bv_term_small_rw_477 := by
  intro h
  have hbad : ¬ ((bvshl (literal 2 1) (bvlshr (literal 2 3) (bvmul (literal 2 3) (literal 2 3)))) = (bvlshr (literal 2 1) (bvlshr (literal 2 3) (bvmul (literal 2 3) (literal 2 3))))) := by decide
  exact hbad (h 2 (literal 2 1) (literal 2 3))

theorem bv_term_small_rw_477_restricted
    (n : Nat) (s t : BitVec n)
    (h : t.toNat < 2 ^ ((t.toNat * t.toNat) % 2 ^ n) ∨
      n * 2 ^ ((t.toNat * t.toNat) % 2 ^ n) ≤ t.toNat) :
    (bvshl s (bvlshr t (bvmul t t))) = (bvlshr s (bvlshr t (bvmul t t))) := by
  apply bvshl_eq_bvlshr_bvlshr_of_lt_or_le
  simpa only [toNat_bvmul] using h

theorem bv_term_small_rw_477_counterexample_width10 :
    bvshl (literal 10 1)
        (bvlshr (literal 10 515) (bvmul (literal 10 515) (literal 10 515))) ≠
      bvlshr (literal 10 1)
        (bvlshr (literal 10 515) (bvmul (literal 10 515) (literal 10 515))) := by decide

/- 数学分析：
固定内层 t 时，所有外层 s 都成立当且仅当 q=0 或 q>=n；对固定 s 还存在额外相等位模式，完整条件是 ShiftBalanced。位宽条件是小平方余数的根不落入禁区。
输入与全输入位宽的充要条件分别见 `_iff`、`_width_iff`。
进一步的位宽算术判据与待形式化部分见 ../EXACT_CONDITIONS.md。
-/

theorem bv_term_small_rw_477_iff (n : Nat) (s t : BitVec n) :
    ((bvshl s (bvlshr t (bvmul t t))) = (bvlshr s (bvlshr t (bvmul t t)))) ↔
      ShiftBalanced n s.toNat (t.toNat / 2 ^ ((t.toNat * t.toNat) % 2 ^ n)) := by
  simpa only [ShiftBalanced, toNat_bvlshr, toNat_bvmul] using
    (bvshl_eq_bvlshr_iff_dvd s (bvlshr t (bvmul t t)))

theorem bv_term_small_rw_477_width_iff (n : Nat) :
    (∀ s t : BitVec n, (bvshl s (bvlshr t (bvmul t t))) = (bvlshr s (bvlshr t (bvmul t t)))) ↔
      SquareWidth477 n := by
  have hpoint : (∀ s t : BitVec n, (bvshl s (bvlshr t (bvmul t t))) = (bvlshr s (bvlshr t (bvmul t t)))) ↔
      ∀ s t : BitVec n, ShiftBalanced n s.toNat (t.toNat / 2 ^ ((t.toNat * t.toNat) % 2 ^ n)) := by
    constructor
    · intro h s t; exact (bv_term_small_rw_477_iff n s t).mp (h s t)
    · intro h s t; exact (bv_term_small_rw_477_iff n s t).mpr (h s t)
  rw [hpoint]
  rw [forall_bitvec_toNat_iff (n := n) (fun a d => ShiftBalanced n a (d / 2 ^ ((d * d) % 2 ^ n)))]
  constructor
  · intro h r hr d hd he
    have hq : d / 2 ^ r < 2 ^ n := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hd
    have hall : ∀ a, a < 2 ^ n → ShiftBalanced n a (d / 2 ^ r) := by
      intro a ha
      simpa only [he] using h a ha d hd
    have hc := (forall_shiftBalanced_iff hq).mp hall
    rcases hc with hc | hc
    · exact Or.inl ((Nat.div_eq_zero_iff.mp hc).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos r)))
    · exact Or.inr ((Nat.le_div_iff_mul_le (Nat.two_pow_pos r)).mp hc)
  · intro h a ha d hd
    by_cases hr : (d * d) % 2 ^ n < n
    · have hc := h _ hr d hd rfl
      have hq : d / 2 ^ ((d * d) % 2 ^ n) < 2 ^ n := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hd
      apply (forall_shiftBalanced_iff hq).mpr _ a ha
      rcases hc with hc | hc
      · exact Or.inl (Nat.div_eq_of_lt hc)
      · exact Or.inr ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr hc)
    · have hp : 2 ^ n ≤ 2 ^ ((d * d) % 2 ^ n) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hd hp)]
      exact shiftBalanced_zero n a

end BV.QF_BV.Unsat
