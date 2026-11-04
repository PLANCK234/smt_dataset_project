/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_309.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvshl_self_bvlshr_bvshl (x : BitVec n) :
    bvshl x (bvlshr x (bvshl x x)) = bvlshr x (bvlshr x (bvshl x x)) := by
  rw [bvlshr_bvshl_self_eq_ite]
  split
  · rename_i h
    rw [h, bvlshr_self]
  · rw [bvshl_zero, bvlshr_zero]

theorem bv_term_small_rw_309 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvlshr s (bvshl s s))) = (bvlshr s (bvlshr s (bvshl s s))) := by
  intro n s t
  simp only [bvshl_self_bvlshr_bvshl]

end BV.QF_BV.Unsat
