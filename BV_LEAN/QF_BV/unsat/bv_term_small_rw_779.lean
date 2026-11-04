/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_779.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_779 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor s (bvand (bvshl t s) t)) = (bvadd s (bvand t (bvshl t s))) := by
  intro n s t
  simp only [bvand_comm, bvand_bvshl_self, bvand_bvand_eq_zero_of_right,
      bvor_eq_bvadd_of_bvand_eq_zero]

end BV.QF_BV.Unsat
