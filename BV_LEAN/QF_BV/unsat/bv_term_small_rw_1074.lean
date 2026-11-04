/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1074.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (shiftLeft_eq')

theorem bv_term_small_rw_1074 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvmul t (bvmul s (bvshl s s))) = (bvmul s (bvmul s (bvshl t s))) := by
  intro n s t
  simp only [bvmul_bvshl_comm] <;> simp only [bvmul, bvshl_eq_shiftLeft, shiftLeft_eq'] <;> ac_rfl

end BV.QF_BV.Unsat
