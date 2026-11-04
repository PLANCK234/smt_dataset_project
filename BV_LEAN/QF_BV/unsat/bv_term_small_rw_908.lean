/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_908.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_908 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvshl (bvshl t t) s)) = (bvshl s (bvshl (bvshl t s) t)) := by
  intro n s t
  simp only [bvshl_bvshl_comm]

end BV.QF_BV.Unsat
