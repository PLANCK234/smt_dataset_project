/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_198.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvneg_bvor_bvneg (x : BitVec n) :
    bvneg (bvor x (bvneg x)) = bvand x (bvneg x) := by
  rw [← bvneg_bvand_bvneg, bvneg_bvneg]

theorem bv_term_small_rw_198 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvneg (bvor s (bvneg s))) = (bvand s (bvneg s)) := by
  intro n s t
  simp only [bvneg_bvor_bvneg]

end BV.QF_BV.Unsat
