/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1125.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1125 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvmul t (bvshl (bvadd s s) s)) = (bvmul s (bvshl (bvadd t t) s)) := by
  intro n s t
  simp only [bvshl_bvadd, bvmul_bvadd]
  rw [bvmul_bvshl_comm t s s]

end BV.QF_BV.Unsat
