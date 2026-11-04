/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_841.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_841 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvshl (bvmul t t) t)) = (bvadd s (bvmul t (bvshl t t))) := by
  intro n s t
  simp only [bvshl_bvmul]

end BV.QF_BV.Unsat
