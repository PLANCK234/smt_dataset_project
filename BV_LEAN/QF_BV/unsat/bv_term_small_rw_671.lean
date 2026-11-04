/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_671.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Bitwise

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (add_assoc not_neg sub_eq_add_neg)

private theorem bvadd_bvnot_bvneg (x y : BitVec n) :
    bvadd x (bvnot (bvneg y)) = bvnot (bvneg (bvadd x y)) := by
  simp only [bvadd, bvnot, bvneg, not_neg,
    sub_eq_add_neg, add_assoc]

theorem bv_term_small_rw_671 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvadd (bvnot (literal n 0)) t)) = (bvnot (bvneg (bvadd s t))) := by
  intro n s t
  simp only [bvadd_comm, bvadd_bvnot_zero, bvadd_bvnot_bvneg]

end BV.QF_BV.Unsat
