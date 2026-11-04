/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1412.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (not_zero ushiftRight_eq')

private theorem bvlshr_bvnot_self (x : BitVec n) :
    bvlshr (bvnot x) x = bvlshr (bvnot (literal n 0)) x := by
  rw [← bvor_bvnot x, bvlshr_bvor, bvlshr_self]
  simp [bvor, literal]

theorem bv_term_small_rw_1412 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvnot (bvor s t)) s) = (bvlshr (bvnot t) s) := by
  intro n s t
  simp only [bvnot_bvor, bvlshr_bvand, bvlshr_bvnot_self,
      bvand_comm] <;> simp only [bvand, bvlshr, bvnot, ushiftRight_eq', literal,
      not_zero] <;> grind

end BV.QF_BV.Unsat
