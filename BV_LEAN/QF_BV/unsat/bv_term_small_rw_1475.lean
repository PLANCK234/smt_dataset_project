/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1475.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1475 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand (bvand s (bvshl s t)) t) = (literal n 0) := by
  intro n s t
  simp only [bvand_comm, bvand_bvshl_self, bvand_bvand_eq_zero_of_right]

end BV.QF_BV.Unsat
