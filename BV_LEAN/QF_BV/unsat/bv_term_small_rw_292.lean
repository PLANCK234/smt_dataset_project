/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_292.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvor_bvshl_self_bvneg (x : BitVec n) :
    bvor x (bvshl x (bvneg x)) = x := by
  rw [← bvand_bvshl_self_bvneg x, bvor_bvand_absorb]

theorem bv_term_small_rw_292 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor s (bvshl s (bvneg s))) = s := by
  intro n s t
  simp only [bvor_bvshl_self_bvneg]

end BV.QF_BV.Unsat
