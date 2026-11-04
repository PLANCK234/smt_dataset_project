/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1055.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1055 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvmul t (bvshl s (bvneg s))) = (bvmul s (bvshl t (bvneg s))) := by
  intro n s t
  simp only [bvmul_bvshl_comm]

end BV.QF_BV.Unsat
