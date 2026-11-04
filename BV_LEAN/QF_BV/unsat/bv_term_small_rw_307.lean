/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_307.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvand_bvlshr_bvshl_self (x y : BitVec n) :
    bvand x (bvlshr x (bvshl y x)) = bvlshr x (bvshl y x) := by
  rw [bvlshr_bvshl_self_eq_ite]
  split <;> simp only [bvand_self, bvand_zero]

theorem bv_term_small_rw_307 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand s (bvlshr s (bvshl s s))) = (bvlshr s (bvshl s s)) := by
  intro n s t
  simp only [bvand_bvlshr_bvshl_self]

end BV.QF_BV.Unsat
