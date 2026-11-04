/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_378.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_378 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvor t (bvnot t))) = (literal n 0) := by
  intro n s t
  simp only [bvor_bvnot, bvshl_bvnot_zero]

end BV.QF_BV.Unsat
