/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_26.smt2
License: CC BY 4.0
-/
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open _root_.BitVec (add_neg_eq_sub neg_one_eq_allOnes not_neg not_zero)

theorem bv_term_small_rw_26 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvnot (literal n 0))) = (bvnot (bvneg s)) := by
  intro n s t
  simp only [bvadd, bvnot, literal, bvneg,
    not_zero, ← neg_one_eq_allOnes,
    add_neg_eq_sub]
  exact (not_neg s).symm

end BV.QF_BV.Unsat
