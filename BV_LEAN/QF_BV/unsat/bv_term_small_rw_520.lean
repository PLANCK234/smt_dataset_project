/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_520.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_520 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvand t (bvshl t t))) = s := by
  intro n s t
  simp only [bvand_bvshl_self, bvshl_zero]

end BV.QF_BV.Unsat
