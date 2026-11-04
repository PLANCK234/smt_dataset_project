/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_675.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Bitwise

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_675 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor s (bvadd (bvnot (literal n 0)) t)) = (bvor s (bvnot (bvneg t))) := by
  intro n s t
  simp only [bvadd_comm, bvadd_bvnot_zero]

end BV.QF_BV.Unsat
