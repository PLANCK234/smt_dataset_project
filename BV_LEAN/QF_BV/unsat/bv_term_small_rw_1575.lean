/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1575.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (shiftLeft_eq' ushiftRight_eq')

theorem bv_term_small_rw_1575 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvand (bvshl t s) t) s) = (bvand (bvlshr (bvor s t) s) t) := by
  intro n s t
  simp only [bvand_comm, bvlshr_bvand, bvlshr_bvor, bvlshr_self,
      bvor_comm, bvor_zero] <;> simp only [bvand, bvlshr, ushiftRight_eq', bvshl_eq_shiftLeft,
      shiftLeft_eq'] <;> grind

end BV.QF_BV.Unsat
