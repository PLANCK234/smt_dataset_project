/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: BV/QF_BV/unsat/bv-term-small-rw_813.smt2
Original status: unknown; proved UNSAT.
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat
open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_813 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvshl (bvmul t t) s)) = (bvadd s (bvmul t (bvshl t s))) := by
  intro n s t
  simp only [bvshl_eq_shiftLeft, _root_.BitVec.shiftLeft_eq', bvmul,
    _root_.BitVec.shiftLeft_eq_mul_twoPow]
  ac_rfl

end BV.QF_BV.Unsat
