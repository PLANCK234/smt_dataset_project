/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1328.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvand_bvshl_bvshl_self (x y z : BitVec n) :
    bvand x (bvshl z (bvshl y x)) = bvand (bvlshr x (bvshl y x)) z := by
  by_cases h : bvshl y x = literal n 0
  · rw [h, bvshl_zero, bvlshr_zero]
  · rw [bvlshr_bvshl_self_eq_ite, ite_eq_right h]
    have hx := lt_toNat_bvshl_of_ne_zero x y h
    rw [bvand_bvshl_eq_zero_of_lt x z _ (Nat.lt_trans hx Nat.lt_two_pow_self)]
    simp [bvand, literal]

private theorem bvlshr_bvand_bvshl_self (x y z : BitVec n) :
    bvlshr (bvand x z) (bvshl y x) = bvand x (bvshl z (bvshl y x)) := by
  rw [bvand_bvshl_bvshl_self, bvlshr_bvand]
  by_cases h : bvshl y x = literal n 0
  · simp only [h, bvlshr_zero]
  · rw [bvlshr_bvshl_self_eq_ite, ite_eq_right h]
    simp [bvand, literal]

theorem bv_term_small_rw_1328 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvand s t) (bvshl s s)) = (bvand s (bvshl t (bvshl s s))) := by
  intro n s t
  exact bvlshr_bvand_bvshl_self s s t

end BV.QF_BV.Unsat
