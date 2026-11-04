/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1115.smt2
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

theorem bv_term_small_rw_1115 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd t (bvlshr t (bvor s t))) = (bvadd (bvlshr s s) t) := by
  intro n s t
  simp only [bvlshr_bvor_right, bvadd_zero, bvlshr_self, bvadd_comm]

end BV.QF_BV.Unsat
