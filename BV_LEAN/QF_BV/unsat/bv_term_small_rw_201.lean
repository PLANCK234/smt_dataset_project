/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_201.smt2
License: CC BY 4.0
-/
import Init.Data.BitVec.Bootstrap
import SMT.BitVec.Rewrite.Arithmetic
import SMT.BitVec.Rewrite.Bitwise
import SMT.Nat.Or

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open _root_.BitVec (add_assoc add_comm neg_add not_eq_neg_add sub_eq_add_neg)

private theorem bvnot_bvadd_bvneg (x y : BitVec n) :
    bvnot (bvadd x (bvneg y)) = bvadd (bvnot x) y := by
  simp [bvnot, bvadd, bvneg, not_eq_neg_add, neg_add,
    sub_eq_add_neg, add_assoc, add_comm]

theorem bv_term_small_rw_201 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvnot (bvadd s (bvneg t))) = (bvadd (bvnot s) t) := by
  intro n s t
  simp only [bvnot_bvadd_bvneg, bvadd_comm]

end BV.QF_BV.Unsat
