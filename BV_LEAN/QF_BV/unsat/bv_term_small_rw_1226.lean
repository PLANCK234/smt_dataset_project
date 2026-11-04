/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1226.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Carry

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1226 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand (bvnot s) (bvadd s s)) = (bvand (bvneg s) (bvadd s s)) := by
  intro n s t
  exact bvand_bvnot_bvadd_self s

end BV.QF_BV.Unsat
