/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_303.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvor_left (x y : BitVec n) :
    bvlshr x (bvor x y) = literal n 0 :=
  bvlshr_eq_zero_of_le x _ SMT.Nat.left_le_or

private theorem bvlshr_bvadd_bvshl_self (x y : BitVec n) :
    bvlshr x (bvadd x (bvshl y x)) = literal n 0 := by
  rw [← bvor_bvshl_self, bvlshr_bvor_left]

theorem bv_term_small_rw_303 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvadd s (bvshl s s))) = (literal n 0) := by
  intro n s t
  simp only [bvlshr_bvadd_bvshl_self]

end BV.QF_BV.Unsat
