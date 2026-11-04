/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1239.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Carry

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1239 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvadd s s) (bvnot s)) = (bvshl s (bvneg s)) := by
  intro n s t
  exact bvshl_bvadd_self_bvnot_same s

end BV.QF_BV.Unsat
