/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1237.smt2
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

theorem bv_term_small_rw_1237 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvnot (literal n 0)) (bvor s t)) = (bvlshr (bvnot s) (bvor s t)) := by
  intro n s t
  simp only [bvlshr_bvor_left, bvlshr_bvnot_of_eq_zero]

end BV.QF_BV.Unsat
