/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_783.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_783 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand s (bvor (bvshl t s) t)) = (bvand s t) := by
  intro n s t
  simp only [bvor_comm, bvand_bvor, bvand_bvshl_self, bvand_zero,
      bvor_eq_bvadd_of_bvand_eq_zero, bvadd_zero]

end BV.QF_BV.Unsat
