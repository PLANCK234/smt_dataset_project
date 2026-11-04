/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1493.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvlshr_bvshl_or_self (x y z : BitVec n) :
    bvlshr (bvlshr x z) (bvshl y x) = bvlshr x (bvor z (bvshl y x)) := by
  by_cases h : bvshl y x = literal n 0
  · rw [h, bvlshr_zero, bvor_zero]
  · have hx := Nat.le_of_lt (lt_toNat_bvshl_of_ne_zero x y h)
    rw [bvlshr_eq_zero_of_le x (bvor z (bvshl y x))
      (Nat.le_trans hx SMT.Nat.right_le_or)]
    apply bvlshr_eq_zero_of_le
    rw [toNat_bvlshr]
    exact Nat.le_trans (Nat.div_le_self _ _) hx

theorem bv_term_small_rw_1493 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvlshr s (bvshl t s)) t) = (bvlshr s (bvor t (bvshl t s))) := by
  intro n s t
  rw [bvlshr_bvlshr_comm]
  exact bvlshr_bvlshr_bvshl_or_self s t t

end BV.QF_BV.Unsat
