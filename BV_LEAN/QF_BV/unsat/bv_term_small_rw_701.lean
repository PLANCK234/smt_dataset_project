/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_701.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (neg_mul neg_zero not_eq_neg_add one_mul shiftLeft_eq' zero_sub)

theorem bv_term_small_rw_701 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvmul s (bvshl (bvnot (literal n 0)) t)) = (bvneg (bvshl s t)) := by
  intro n s t
  simp only [bvmul_bvshl_comm] <;> simp only [bvmul, bvnot, literal, not_eq_neg_add, neg_zero,
      zero_sub, bvshl_eq_shiftLeft, shiftLeft_eq', neg_mul, one_mul,
      bvneg] <;> grind

end BV.QF_BV.Unsat
