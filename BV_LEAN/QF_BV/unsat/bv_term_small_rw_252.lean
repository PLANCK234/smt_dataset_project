/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_252.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Quotient

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvnot_bvlshr_self (x y : BitVec n) :
    bvlshr x (bvnot (bvlshr y x)) = literal n 0 := by
  by_cases hx : x = literal n 0
  · subst x; simp [bvlshr, literal]
  · exact bvlshr_large x _ (width_le_toNat_bvnot_bvlshr x y hx)

theorem bv_term_small_rw_252 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvnot (bvlshr t s))) = (literal n 0) := by
  intro n s t
  simp only [bvlshr_bvnot_bvlshr_self]

end BV.QF_BV.Unsat
