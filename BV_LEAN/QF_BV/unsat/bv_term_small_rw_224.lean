/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_224.smt2
License: CC BY 4.0
-/
import Init.Data.BitVec.Bootstrap
import SMT.BitVec.Rewrite.Arithmetic
import SMT.BitVec.Rewrite.Bitwise
import SMT.Nat.Or

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open _root_.BitVec (add_assoc neg_sub not_eq_neg_add)

private theorem bvadd_bvneg_bvnot (x y : BitVec n) :
    bvadd x (bvneg (bvnot y)) = bvneg (bvnot (bvadd x y)) := by
  simp [bvadd, bvnot, bvneg, not_eq_neg_add, neg_sub,
    add_assoc]

theorem bv_term_small_rw_224 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvneg (bvnot s))) = (bvneg (bvnot (bvadd s s))) := by
  intro n s t
  simp only [bvadd_bvneg_bvnot]

end BV.QF_BV.Unsat
