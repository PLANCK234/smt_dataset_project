/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1408.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import LEMMAS_learned.Nat.Div
import LEMMAS_learned.Nat.Pow
import SMT.BitVec.ToNat.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvneg_bvadd_self (x : BitVec n) :
    bvlshr (bvneg (bvadd x x)) x = bvlshr (bvneg x) x := by
  by_cases hx : x = literal n 0
  · subst x; rw [bvadd_zero]
  by_cases hn : n ≤ x.toNat
  · rw [bvlshr_large _ _ hn, bvlshr_large _ _ hn]
  have hx0 : 0 < x.toNat := by
    apply Nat.pos_of_ne_zero
    intro h; apply hx; apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using h
  have hpow : 2 ^ x.toNat < 2 ^ n := Nat.pow_lt_pow_right (by decide) (Nat.lt_of_not_ge hn)
  have hdouble := Learned.Nat.two_mul_le_two_pow (n := x.toNat)
  have hlt := x.isLt
  have hp := Nat.two_pow_pos n
  have hd : 2 ^ x.toNat ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
  apply toNat_injective
  simp only [toNat_bvlshr, toNat_bvneg, toNat_bvadd]
  rw [Nat.mod_eq_of_lt (show x.toNat + x.toNat < 2 ^ n by omega),
    Nat.mod_eq_of_lt (show 2 ^ n - (x.toNat + x.toNat) < 2 ^ n by omega),
    Nat.mod_eq_of_lt (show 2 ^ n - x.toNat < 2 ^ n by omega)]
  rw [Learned.Nat.sub_div_eq_pred_of_dvd hd (by omega) (by omega) (by omega),
    Learned.Nat.sub_div_eq_pred_of_dvd hd hx0 (by omega) (by omega)]

theorem bv_term_small_rw_1408 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvneg (bvadd s s)) s) = (bvlshr (bvneg s) s) := by
  intro n s t
  exact bvlshr_bvneg_bvadd_self s

end BV.QF_BV.Unsat
