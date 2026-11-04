/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1415.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvor_bvneg_bvshl_self (x y : BitVec n) :
    bvor x (bvneg (bvshl y x)) = bvadd x (bvneg (bvshl y x)) := by
  rw [← bvshl_bvneg, bvor_bvshl_self]

theorem bv_term_small_rw_1415 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor (bvneg (bvshl s t)) t) = (bvadd (bvneg (bvshl s t)) t) := by
  intro n s t
  simp only [bvor_comm, bvor_bvneg_bvshl_self, bvadd_comm]

end BV.QF_BV.Unsat
