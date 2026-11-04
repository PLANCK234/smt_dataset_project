/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_443.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvor_right (x y : BitVec n) :
    bvlshr y (bvor x y) = literal n 0 :=
  bvlshr_eq_zero_of_le y _ SMT.Nat.right_le_or

theorem bv_term_small_rw_443 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvlshr t (bvor s t))) = s := by
  intro n s t
  simp only [bvlshr_bvor_right, bvshl_zero]

end BV.QF_BV.Unsat
