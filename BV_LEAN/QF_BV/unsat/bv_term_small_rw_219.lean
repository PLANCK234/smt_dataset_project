/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_219.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_219 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvneg (bvmul (bvnot (literal n 0)) t)) = (bvadd (bvlshr s s) t) := by
  intro n s t
  simp only [bvmul_comm, bvmul_bvnot_zero, bvneg_bvneg, bvlshr_self,
      bvadd_comm, bvadd_zero]

end BV.QF_BV.Unsat
