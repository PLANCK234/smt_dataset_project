/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_251.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Quotient

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvshl_bvneg_bvlshr_self (x y : BitVec n) :
    bvshl x (bvneg (bvlshr y x)) = bvlshr x (bvneg (bvlshr y x)) := by
  by_cases hx : x = literal n 0
  · subst x; simp [bvshl_eq_shiftLeft, bvlshr, literal]
  by_cases hq : bvlshr y x = literal n 0
  · rw [hq]; simp [bvneg, literal, bvshl_zero]
  have hn := width_le_toNat_bvnot_bvlshr x y hx
  have hq0 : 0 < (bvlshr y x).toNat := by
    have hz : (bvlshr y x).toNat ≠ 0 := by
      intro h; apply hq; apply toNat_injective; simpa only [toNat_literal, Nat.zero_mod] using h
    omega
  have hq' := (bvlshr y x).isLt
  have hp := Nat.two_pow_pos n
  have hneg : n ≤ (bvneg (bvlshr y x)).toNat := by
    rw [toNat_bvneg, Nat.mod_eq_of_lt (by omega)]
    rw [toNat_bvnot] at hn
    omega
  rw [bvshl_large _ _ hneg, bvlshr_large _ _ hneg]

theorem bv_term_small_rw_251 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvneg (bvlshr t s))) = (bvlshr s (bvneg (bvlshr t s))) := by
  intro n s t
  simp only [bvshl_bvneg_bvlshr_self]

end BV.QF_BV.Unsat
