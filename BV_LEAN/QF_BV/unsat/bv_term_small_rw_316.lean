/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_316.smt2
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

theorem bv_term_small_rw_316 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor s (bvshl s (bvor s t))) = (bvadd s (bvshl s (bvor s t))) := by
  intro n s t
  simp only [bvor_bvshl_bvor_left]

end BV.QF_BV.Unsat
