/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_289.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (add_assoc add_right_neg zero_add)

private theorem bvadd_bvor_bvneg (x y : BitVec n) :
    bvadd x (bvor y (bvneg x)) = bvand y (bvnot (bvneg x)) := by
  rw [bvor_comm y, ← bvadd_bvand_bvnot]
  change x + (-x + bvand y (bvnot (bvneg x))) = _
  rw [← add_assoc, add_right_neg, zero_add]

theorem bv_term_small_rw_289 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvor s (bvneg s))) = (bvand s (bvnot (bvneg s))) := by
  intro n s t
  simp only [bvadd_bvor_bvneg]

end BV.QF_BV.Unsat
