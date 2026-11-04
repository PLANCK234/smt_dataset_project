/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_605.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Quotient

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvshl_bvlshr_bvneg_self (x : BitVec n) :
    bvshl x (bvlshr (bvnot x) x) = bvshl x (bvlshr (bvneg x) x) := by
  by_cases hx : x = literal n 0
  · subst x; simp [bvshl_eq_shiftLeft, literal]
  · rw [bvlshr_bvneg_self_of_ne_zero x hx]

theorem bv_term_small_rw_605 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvlshr (bvnot s) s)) = (bvshl s (bvlshr (bvneg s) s)) := by
  intro n s t
  exact bvshl_bvlshr_bvneg_self s

end BV.QF_BV.Unsat
