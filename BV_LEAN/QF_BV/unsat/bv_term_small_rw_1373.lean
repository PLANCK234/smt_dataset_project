/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1373.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Carry

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1373 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd (bvor s t) (bvor s t)) = (bvor (bvadd s s) (bvadd t t)) := by
  intro n s t
  simp only [bvadd_bvor_double]

end BV.QF_BV.Unsat
