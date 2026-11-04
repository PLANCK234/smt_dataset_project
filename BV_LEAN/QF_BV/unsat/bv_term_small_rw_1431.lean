/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1431.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Bitwise

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1431 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd (bvadd s (bvnot t)) t) = (bvnot (bvneg s)) := by
  intro n s t
  rw [bvadd_assoc, bvadd_comm (bvnot t), bvadd_bvnot, bvadd_bvnot_zero]

end BV.QF_BV.Unsat
