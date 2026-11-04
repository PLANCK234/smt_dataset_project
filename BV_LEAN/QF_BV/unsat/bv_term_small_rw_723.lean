/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_723.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Quotient

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

/-
数学分析：
令 a = s.toNat，q = (t >> s).toNat。s 或 q 为零时直接化简。
非零分支满足 q*2^a ≤ t.toNat < 2^n，因此 q << s 不溢出，且至少为 2^a > a，
左侧右移为零。负商下界给出 (-q).toNat ≥ n，右侧同样为零。
-/

theorem bv_term_small_rw_723 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvshl (bvlshr t s) s)) = (bvlshr s (bvneg (bvlshr t s))) := by
  intro n s t
  by_cases hs : s = literal n 0
  · subst s
    simp [bvlshr, literal]
  by_cases hq : bvlshr t s = literal n 0
  · rw [hq]
    simp [bvneg, bvshl_eq_shiftLeft, literal]
  have hq0 : 0 < (bvlshr t s).toNat := by
    apply Nat.pos_of_ne_zero
    intro h
    apply hq
    apply toNat_injective
    simpa only [toNat_literal, Nat.zero_mod] using h
  have hdiv : (bvlshr t s).toNat * 2 ^ s.toNat ≤ t.toNat := by
    rw [toNat_bvlshr]
    exact Nat.div_mul_le_self _ _
  have ht := t.isLt
  have hneg := width_le_toNat_bvneg_bvlshr s t hs hq
  rw [bvlshr_large _ _ hneg]
  apply bvlshr_eq_zero_of_le
  rw [toNat_bvshl, Nat.mod_eq_of_lt (by omega)]
  have h := Nat.mul_le_mul_right (2 ^ s.toNat) hq0
  simp only [Nat.one_mul] at h
  exact Nat.le_trans (Nat.le_of_lt Nat.lt_two_pow_self) h

end BV.QF_BV.Unsat
