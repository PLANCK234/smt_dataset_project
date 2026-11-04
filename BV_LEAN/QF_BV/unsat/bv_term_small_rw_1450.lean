/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1450.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvshl_bvlshr_bvshl_self (x : BitVec n) :
    bvshl (bvlshr x (bvshl x x)) x = literal n 0 := by
  rw [bvlshr_bvshl_self_eq_ite]
  split
  · assumption
  · simp [bvshl_eq_shiftLeft, literal]

theorem bv_term_small_rw_1450 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvlshr s (bvshl s s)) s) = (literal n 0) := by
  intro n s t
  simp only [bvshl_bvlshr_bvshl_self]

end BV.QF_BV.Unsat
