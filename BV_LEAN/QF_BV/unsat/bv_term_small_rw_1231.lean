/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1231.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1231 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand (bvnot s) (bvshl t s)) = (bvshl t s) := by
  intro n s t
  rw [bvand_comm]
  exact bvand_bvnot_of_bvand_eq_zero _ _ (by
    rw [bvand_comm, bvand_bvshl_self])

end BV.QF_BV.Unsat
