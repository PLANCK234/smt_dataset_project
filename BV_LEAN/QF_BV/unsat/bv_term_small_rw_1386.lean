/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1386.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1386 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand (bvor s t) (bvshl t t)) = (bvand s (bvshl t t)) := by
  intro n s t
  rw [bvand_comm, bvand_bvor]
  simp only [bvand_comm, bvand_bvshl_self, bvor_zero]

end BV.QF_BV.Unsat
