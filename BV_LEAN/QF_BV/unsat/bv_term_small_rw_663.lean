/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_663.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Bitwise

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_663 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvmul s (bvor (bvnot t) t)) = (bvneg s) := by
  intro n s t
  simp only [bvor_comm, bvor_bvnot, bvmul_bvnot_zero]

end BV.QF_BV.Unsat
