/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1489.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1489 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvadd s (bvshl t s)) s) = (bvlshr (bvshl t s) s) := by
  intro n s t
  rw [← bvor_bvshl_self, bvlshr_bvor, bvlshr_self]
  simp [bvor, literal]

end BV.QF_BV.Unsat
