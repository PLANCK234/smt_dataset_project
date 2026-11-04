/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1470.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvor_bvshl_bvor_left (x y z : BitVec n) :
    bvor x (bvshl y (bvor x z)) = bvadd x (bvshl y (bvor x z)) := by
  apply bvor_bvshl_eq_bvadd_of_lt
  exact Nat.lt_of_le_of_lt SMT.Nat.left_le_or Nat.lt_two_pow_self

private theorem bvor_bvshl_bvor_right (x y z : BitVec n) :
    bvor x (bvshl y (bvor z x)) = bvadd x (bvshl y (bvor z x)) := by
  rw [bvor_comm z x, bvor_bvshl_bvor_left]

theorem bv_term_small_rw_1470 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor (bvshl s (bvor s t)) t) = (bvadd (bvshl s (bvor s t)) t) := by
  intro n s t
  simp only [bvor_comm, bvor_bvshl_bvor_right, bvadd_comm]

end BV.QF_BV.Unsat
