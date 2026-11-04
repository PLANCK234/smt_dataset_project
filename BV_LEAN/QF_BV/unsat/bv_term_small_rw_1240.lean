/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1240.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Carry

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1240 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvadd s s) (bvnot t)) = (bvand t (bvshl s (bvneg t))) := by
  intro n s t
  exact bvshl_bvadd_self_bvnot s t

end BV.QF_BV.Unsat
