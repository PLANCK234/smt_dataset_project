/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_418.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Carry

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_418 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand s (bvadd t (bvshl s s))) = (bvand s t) := by
  intro n s t
  simp only [bvand_bvadd_bvshl]

end BV.QF_BV.Unsat
