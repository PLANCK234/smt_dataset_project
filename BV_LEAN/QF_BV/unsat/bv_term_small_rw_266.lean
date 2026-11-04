/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_266.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_266 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvnot (bvlshr t t))) = (bvnot (bvneg s)) := by
  intro n s t
  simp only [bvlshr_self, bvadd_bvnot_zero]

end BV.QF_BV.Unsat
