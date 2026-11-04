/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1073.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1073 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor t (bvadd s (bvshl s s))) = (bvor s (bvor t (bvshl s s))) := by
  intro n s t
  rw [← bvor_bvshl_self]
  ac_rfl

end BV.QF_BV.Unsat
