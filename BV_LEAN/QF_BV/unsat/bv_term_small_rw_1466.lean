/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1466.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1466 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvlshr s (bvlshr s t)) t) = (literal n 0) := by
  intro n s t
  simp only [bvlshr_bvlshr_comm, bvlshr_self]

end BV.QF_BV.Unsat
