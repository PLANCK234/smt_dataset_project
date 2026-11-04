/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1381.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1381 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand (bvor s t) (bvshl t s)) = (bvand t (bvshl t s)) := by
  intro n s t
  rw [bvand_comm, bvand_bvor]
  simp only [bvand_comm, bvand_bvshl_self]
  simp [bvor, literal]

end BV.QF_BV.Unsat
