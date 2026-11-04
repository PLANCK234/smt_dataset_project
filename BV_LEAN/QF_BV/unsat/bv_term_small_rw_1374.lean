/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1374.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Carry

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1374 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd (bvor s t) (bvshl s t)) = (bvor t (bvadd s (bvshl s t))) := by
  intro n s t
  rw [bvor_comm s t, bvadd_bvor_bvshl]

end BV.QF_BV.Unsat
