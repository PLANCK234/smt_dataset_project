/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_247.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_247 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvneg (bvor s t))) = (bvneg (bvand (bvnot s) t)) := by
  intro n s t
  simp only [bvadd_bvneg_bvor, bvand_comm]

end BV.QF_BV.Unsat
