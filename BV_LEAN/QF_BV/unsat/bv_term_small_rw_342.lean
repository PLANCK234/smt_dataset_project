/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_342.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvand_bvshl_bvnot (x y : BitVec n) :
    bvand x (bvshl y (bvnot x)) = bvshl y (bvnot x) := by
  have h := bvand_bvshl_self (bvnot x) y
  rw [bvand_comm] at h
  have := bvand_bvnot_of_bvand_eq_zero _ _ h
  simpa only [bvnot_bvnot, bvand_comm] using this

theorem bv_term_small_rw_342 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand s (bvshl t (bvnot s))) = (bvshl t (bvnot s)) := by
  intro n s t
  simp only [bvand_bvshl_bvnot]

end BV.QF_BV.Unsat
