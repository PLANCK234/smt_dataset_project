/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1293.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1293 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvmul s t) (bvnot s)) = (bvmul s (bvshl t (bvnot s))) := by
  intro n s t
  simp only [bvshl_bvmul, bvmul_bvshl_comm]

end BV.QF_BV.Unsat
