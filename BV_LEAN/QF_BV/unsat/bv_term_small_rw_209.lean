/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: BV/QF_BV/unsat/bv-term-small-rw_209.smt2
Original status: unknown; proved UNSAT.
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat
open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_209 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvneg (bvadd t (bvmul s t))) = (bvmul (bvnot s) t) := by
  intro n s t
  simp only [bvneg, bvnot, bvmul,
    bvadd, _root_.BitVec.not_eq_neg_add, _root_.BitVec.add_mul,
    _root_.BitVec.neg_mul, _root_.BitVec.one_mul, _root_.BitVec.neg_add,
    _root_.BitVec.sub_eq_add_neg]
  ac_rfl

end BV.QF_BV.Unsat
