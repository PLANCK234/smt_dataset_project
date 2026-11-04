/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1521.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (zero_or)

private theorem bvlshr_bvnot_self (x : BitVec n) :
    bvlshr (bvnot x) x = bvlshr (bvnot (literal n 0)) x := by
  rw [← bvor_bvnot x, bvlshr_bvor, bvlshr_self]
  simp [bvor, literal]

theorem bv_term_small_rw_1521 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand (bvlshr (bvnot s) s) t) = (bvlshr (bvadd s (bvshl t s)) s) := by
  intro n s t
  rw [← bvor_bvshl_self, bvlshr_bvor, bvlshr_self,
    bvlshr_bvshl_mask, bvlshr_bvnot_self]
  simp only [bvor, literal, zero_or]
  exact bvand_comm _ _

end BV.QF_BV.Unsat
