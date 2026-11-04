/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1170.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1170 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr t (bvadd (bvmul t (literal n 0)) s)) = (bvlshr (bvor s t) s) := by
  intro n s t
  simp only [bvmul_zero, bvadd_comm, bvadd_zero, bvlshr_bvor,
      bvlshr_self, bvor_comm, bvor_zero]

end BV.QF_BV.Unsat
