/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: BV/QF_BV/unsat/bv-term-small-rw_1518.smt2
Original status: unknown; proved UNSAT.
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat
open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1518 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl (bvmul t (bvor s t)) s) = (bvmul (bvor s t) (bvshl t s)) := by
  intro n s t
  simp only [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq', bvmul,
    _root_.BitVec.shiftLeft_eq_mul_twoPow]
  ac_rfl

end BV.QF_BV.Unsat
