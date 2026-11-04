/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_222.smt2
License: CC BY 4.0
-/
import Init.Data.BitVec.Bootstrap
import SMT.BitVec.Rewrite.Arithmetic
import SMT.BitVec.Rewrite.Bitwise
import SMT.Nat.Or

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open _root_.BitVec (add_assoc not_neg sub_eq_add_neg)

private theorem bvadd_bvnot_bvneg (x y : BitVec n) :
    bvadd x (bvnot (bvneg y)) = bvnot (bvneg (bvadd x y)) := by
  simp only [bvadd, bvnot, bvneg, not_neg,
    sub_eq_add_neg, add_assoc]

theorem bv_term_small_rw_222 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvnot (bvneg s))) = (bvnot (bvneg (bvadd s s))) := by
  intro n s t
  simp only [bvadd_bvnot_bvneg]

end BV.QF_BV.Unsat
