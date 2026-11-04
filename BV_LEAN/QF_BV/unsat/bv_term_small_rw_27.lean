/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_27.smt2
License: CC BY 4.0
-/
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open _root_.BitVec (mul_neg mul_one neg_one_eq_allOnes not_zero)

theorem bv_term_small_rw_27 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvmul s (bvnot (literal n 0))) = (bvneg s) := by
  intro n s t
  simp only [bvmul, bvnot, literal, bvneg,
    not_zero, ← neg_one_eq_allOnes,
    mul_neg, mul_one]

end BV.QF_BV.Unsat
