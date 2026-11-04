/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1128.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1128 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvmul t (bvshl (bvshl s s) t)) = (bvmul s (bvshl (bvshl t s) t)) := by
  intro n s t
  simp only [← bvshl_bvmul, bvmul_comm]

end BV.QF_BV.Unsat
