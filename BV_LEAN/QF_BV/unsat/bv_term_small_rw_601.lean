/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_601.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Quotient

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvnot_self (x : BitVec n) :
    bvlshr (bvnot x) x = bvlshr (bvnot (literal n 0)) x := by
  rw [← bvor_bvnot x, bvlshr_bvor, bvlshr_self]
  simp [bvor, literal]

private theorem bvand_bvlshr_bvneg_self (x : BitVec n) :
    bvand x (bvlshr (bvneg x) x) = bvlshr (bvshl x x) x := by
  by_cases hx : x = literal n 0
  · subst x; simp [bvand, bvshl_eq_shiftLeft, bvlshr, literal]
  · rw [bvlshr_bvneg_self_of_ne_zero x hx, bvlshr_bvnot_self, bvlshr_bvshl_mask]

theorem bv_term_small_rw_601 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand s (bvlshr (bvneg s) s)) = (bvlshr (bvshl s s) s) := by
  intro n s t
  exact bvand_bvlshr_bvneg_self s

end BV.QF_BV.Unsat
