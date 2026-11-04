/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_765.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Carry

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_765 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand s (bvadd (bvshl t s) t)) = (bvand s t) := by
  intro n s t
  simp only [bvadd_comm, bvand_bvadd_bvshl]

end BV.QF_BV.Unsat
