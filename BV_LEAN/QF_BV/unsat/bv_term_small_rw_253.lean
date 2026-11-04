/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_253.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Quotient

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvshl_bvnot_bvlshr_self (x y : BitVec n) :
    bvshl x (bvnot (bvlshr y x)) = literal n 0 := by
  by_cases hx : x = literal n 0
  · subst x; simp [bvshl_eq_shiftLeft, literal]
  · exact bvshl_large x _ (width_le_toNat_bvnot_bvlshr x y hx)

theorem bv_term_small_rw_253 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvnot (bvlshr t s))) = (literal n 0) := by
  intro n s t
  simp only [bvshl_bvnot_bvlshr_self]

end BV.QF_BV.Unsat
