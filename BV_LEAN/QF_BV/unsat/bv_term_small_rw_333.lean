/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_333.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Bitwise

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_333 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvadd t (bvnot s))) = (bvnot (bvneg t)) := by
  intro n s t
  rw [bvadd_comm t, ← bvadd_assoc, bvadd_bvnot, bvadd_comm, bvadd_bvnot_zero]

end BV.QF_BV.Unsat
