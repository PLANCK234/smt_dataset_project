/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_297.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvor_bvshl_bvnot (x y : BitVec n) :
    bvor x (bvshl y (bvnot x)) = x := by
  have h := bvand_bvshl_self (bvnot x) y
  rw [bvand_comm] at h
  have := bvor_bvnot_of_bvand_eq_zero _ _ h
  simpa only [bvnot_bvnot, bvor_comm] using this

theorem bv_term_small_rw_297 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor s (bvshl s (bvnot s))) = s := by
  intro n s t
  simp only [bvor_bvshl_bvnot]

end BV.QF_BV.Unsat
