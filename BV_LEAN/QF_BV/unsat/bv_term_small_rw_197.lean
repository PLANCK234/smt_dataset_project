/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_197.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_197 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvneg (bvand s (bvneg s))) = (bvor s (bvneg s)) := by
  intro n s t
  simp only [bvneg_bvand_bvneg]

end BV.QF_BV.Unsat
