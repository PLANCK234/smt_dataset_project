/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_229.smt2
License: CC BY 4.0
-/
import Init.Data.BitVec.Bootstrap
import SMT.BitVec.Rewrite.Arithmetic
import SMT.BitVec.Rewrite.Bitwise
import SMT.Nat.Or

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open _root_.BitVec (add_assoc add_right_neg neg_add not_eq_neg_add sub_eq_add_neg zero_add)

private theorem bvadd_bvnot_bvadd_self (x : BitVec n) :
    bvadd x (bvnot (bvadd x x)) = bvnot x := by
  simp only [bvadd, bvnot, not_eq_neg_add, neg_add,
    sub_eq_add_neg]
  rw [← add_assoc, ← add_assoc,
    add_right_neg, zero_add]

theorem bv_term_small_rw_229 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvnot (bvadd s s))) = (bvnot s) := by
  intro n s t
  simp only [bvadd_bvnot_bvadd_self]

end BV.QF_BV.Unsat
