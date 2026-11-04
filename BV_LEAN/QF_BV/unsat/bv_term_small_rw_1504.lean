/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1504.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1504 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvmul s (bvshl t t)) t) = (bvmul s (bvshl (bvshl t t) t)) := by
  intro n s t
  simp only [bvmul_bvshl_comm, bvshl_bvmul, bvmul_comm]

end BV.QF_BV.Unsat
