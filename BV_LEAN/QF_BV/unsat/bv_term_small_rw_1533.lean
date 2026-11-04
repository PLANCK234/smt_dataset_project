/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1533.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (neg_mul neg_zero not_eq_neg_add one_mul shiftLeft_eq' zero_sub)

theorem bv_term_small_rw_1533 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvmul (bvnot (literal n 0)) t) s) = (bvmul (bvshl (bvnot (literal n 0)) s) t) := by
  intro n s t
  simp only [bvmul_comm, bvmul_bvnot_zero, bvshl_bvneg,
      bvmul_bvshl_comm] <;> simp only [bvneg, bvshl_eq_shiftLeft, shiftLeft_eq', bvmul,
      bvnot, literal, not_eq_neg_add, neg_zero, zero_sub, neg_mul,
      one_mul] <;> grind

end BV.QF_BV.Unsat
