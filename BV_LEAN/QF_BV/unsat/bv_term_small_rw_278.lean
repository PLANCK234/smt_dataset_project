/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_278.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_278 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvnot (bvmul t (literal n 0)))) = (literal n 0) := by
  intro n s t
  simp only [bvmul_zero, bvlshr_bvnot_zero]

end BV.QF_BV.Unsat
