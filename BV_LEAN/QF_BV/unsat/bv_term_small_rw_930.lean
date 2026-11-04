/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_930.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_930 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvor (bvshl t t) t)) = (bvlshr s (bvadd t (bvshl t t))) := by
  intro n s t
  simp only [bvor_comm, bvor_bvshl_self]

end BV.QF_BV.Unsat
