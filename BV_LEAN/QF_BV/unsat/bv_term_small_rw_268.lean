/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_268.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_268 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvnot (bvlshr t t))) = (literal n 0) := by
  intro n s t
  simp only [bvlshr_self, bvshl_bvnot_zero]

end BV.QF_BV.Unsat
