/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1507.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1507 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor (bvand s (bvshl t t)) t) = (bvadd (bvand s (bvshl t t)) t) := by
  intro n s t
  simp only [bvand_comm, bvand_bvshl_self, bvand_bvand_eq_zero_of_right,
      bvor_eq_bvadd_of_bvand_eq_zero, bvadd_comm]

end BV.QF_BV.Unsat
